; fn: the record log's open tells a torn tail from damage (lane log-corruption,
; 2026-09-27; fuzz-nntp's F3).
;
; The stream (books/store-log-stream.lisp) reads entries from the front while
; each one validates and names the previous trailer, and stops at the first
; that does not.  Before this book the stop WAS the end of the log: one bit
; flipped in the first entry of a twelve-record segment answered an empty
; history with exit 0, and a writable open then zeroed the eleven committed
; entries after it (fn-lg-recover-tail).  A crash cannot produce that image:
; the log has at most ONE pending write (fn-lgc-append-admitsp: nothing in
; flight), at the frontier, over the segment's preallocated zeros
; (books/store-log-crash.lisp), so past the stop of a crash image lies only
; that write's torn remainder and zeros.
;
; The PROBE: after the stream stops at P, the host reads, at every offset
; P, P+U, P+2U, ... below the extent (U the write unit: every entry of the log
; starts on one), the header window ACL2 names (fn-lgdm-header-len), the
; entry length ACL2 answers from it (fn-lgdm-entry-len; NIL: no entry
; starts there) and that entry's octets, and ACL2 steps (fn-lgdm-step): an
; entry that validates as a chained frame of this log under the predecessor
; it claims (fn-lgdm-valid-p) is a VALID SUCCESSOR, counted and stepped over;
; anything else advances one unit, and a header window that is not all zeros
; is counted as debris.  The VERDICT (fn-lgdm-verdict) is ACL2's:
;
;   :broken   the entry at the stop validates under another predecessor (the
;             existing splice verdict, fn-lgs-chain-broken-p): refused;
;   :damaged  a valid successor exists: the history continues past a damaged
;             entry.  A recovery event, refused by name (fn-lgdm-refusal-text:
;             reason=log-damaged at=SEGMENT:P first-valid=Q valid-after=N
;             records=M); the owner does not start and nothing is written;
;   :torn     no valid successor and some debris: the torn tail of the one
;             pending write, recovered to P (the committed entries), with the
;             debris count reported;
;   :complete no valid successor, no debris.
;
; The operator's repair (store recover --repair truncate SEGMENT:P): ACL2
; admits it only for the :damaged verdict at exactly that segment and offset
; (fn-lgdm-repair-admitsp), and then the open recovers to P as a torn tail
; would; the host first keeps the damaged segment's octets (quarantine/).  No
; other verdict is changed by a repair, and a repair naming another offset is
; refused.
;
; Theorems (the subject is the host's calls: host/native/io.lisp
; fnn-log-stream-segment calls fn-lgdm-start, fn-lgdm-done-p, fn-lgdm-q,
; fn-lgdm-header-len, fn-lgdm-entry-len, fn-lgdm-step and fn-lgdm-verdict after
; the stream's fn-lgw-* loop):
;
;   KEYSTONE fn-lgdm-open-verdict-is-the-classification: over the segment's
;     octets C, the verdict of the probe run after the stream's run is
;     fn-lgdm-classify: the stop is the scan's frontier, the splice verdict is
;     fn-lgs-chain-broken-p's, and the damage point is the least unit-aligned
;     offset at or past the stop where a valid entry starts
;     (fn-lgdm-least-valid).
;   KEYSTONE fn-lgdm-no-silent-prefix: when a valid entry starts at any
;     unit-aligned offset past the stop, the open's verdict is :broken or
;     :damaged, never a recovered prefix; and a :damaged verdict names a
;     valid entry at or past the stop (never a refusal without one).
;   KEYSTONE fn-lgdm-damage-lies-in-the-last-write: for a segment that is a
;     well-formed log L followed by octets Y and then zeros (a crash image of
;     one pending write at L's end has this shape with Y within the write's
;     range, fn-bs-crash-of-aligned-append), a :broken or :damaged verdict
;     points into Y; with Y empty (a clean segment) the verdict is :complete
;     or :torn at L's end, never a refusal.  So the torn-tail case is exactly
;     the last incomplete write; what a crash image can still show past the
;     stop is a frame inside that write's own octets (the batch's later
;     entries, or a record body that embeds a valid frame): refused, never
;     silently read (the residual is the lane's record, fail-closed).

(in-package "ACL2")
(include-book "store-log-stream")
(local (include-book "arithmetic/top" :dir :system))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-lg-entry-okp)
                          (:rewrite fn-lgc-consp-nthcdr)
                          (:rewrite fn-lgw-slice-when-not-declared))))

; -----------------------------------------------------------------------------
; Vocabulary.

; The probe's stride: the write unit (every entry starts on one; an unpadded
; log's unit is one).
(defun fn-lgdm-stride (unit)
  (declare (xargs :guard t))
  (if (posp unit) unit 1))

(defthm fn-lgdm-stride-posp
  (posp (fn-lgdm-stride unit))
  :rule-classes :type-prescription)

; A valid entry: the octets validate as a chained frame of this log under the
; predecessor they claim (fn-lgw-broken-slice-p without its "not the last
; trailer").
(defun fn-lgdm-valid-p (e max)
  (declare (xargs :guard t))
  (and (ec-call (fn-lg-entry-okp e (ec-call (fn-lgs-claimed-prev e max)) max)) t))

; A header window holding an octet that is not zero.
(defun fn-lgdm-nonzero-p (h)
  (declare (xargs :guard t))
  (if (consp h)
      (or (not (equal (car h) 0)) (fn-lgdm-nonzero-p (cdr h)))
    nil))

; -----------------------------------------------------------------------------
; The probe's state: (:lgdm Q FIRST ENTRIES RECORDS DEBRIS).

(defun fn-lgdm-make (q first entries records debris)
  (declare (xargs :guard t))
  (list :lgdm q first entries records debris))

(defun fn-lgdm-q (ps) (declare (xargs :guard (true-listp ps))) (nfix (nth 1 ps)))
(defun fn-lgdm-first (ps) (declare (xargs :guard (true-listp ps))) (nth 2 ps))
(defun fn-lgdm-entries (ps) (declare (xargs :guard (true-listp ps))) (nfix (nth 3 ps)))
(defun fn-lgdm-records (ps) (declare (xargs :guard (true-listp ps))) (nfix (nth 4 ps)))
(defun fn-lgdm-debris (ps) (declare (xargs :guard (true-listp ps))) (nfix (nth 5 ps)))

(defthm fn-lgdm-fields-of-make
  (let ((ps (fn-lgdm-make q first entries records debris)))
    (and (equal (fn-lgdm-q ps) (nfix q))
         (equal (fn-lgdm-first ps) first)
         (equal (fn-lgdm-entries ps) (nfix entries))
         (equal (fn-lgdm-records ps) (nfix records))
         (equal (fn-lgdm-debris ps) (nfix debris)))))

(defthm fn-lgdm-make-true-listp
  (true-listp (fn-lgdm-make q first entries records debris))
  :rule-classes :type-prescription)

(defthm fn-lgdm-q-natp (natp (fn-lgdm-q ps)) :rule-classes :type-prescription)

(in-theory (disable fn-lgdm-make fn-lgdm-q fn-lgdm-first fn-lgdm-entries
                    fn-lgdm-records fn-lgdm-debris))

; -----------------------------------------------------------------------------
; The host's calls.

; From the stream's stopped state: the probe starts at the stop.
(defun fn-lgdm-start (st)
  (declare (xargs :guard (true-listp st)))
  (fn-lgdm-make (fn-lgw-pos st) nil 0 0 0))

(defun fn-lgdm-done-p (ps extent)
  (declare (xargs :guard (true-listp ps)))
  (<= (nfix extent) (fn-lgdm-q ps)))

(defun fn-lgdm-header-len (ps extent)
  (declare (xargs :guard (true-listp ps)))
  (min *fn-frame-header-octets* (nfix (- (nfix extent) (fn-lgdm-q ps)))))

(defun fn-lgdm-entry-len (h ps extent)
  (declare (xargs :guard (true-listp ps)))
  (let ((n (ec-call (fn-lg-declared-len h))))
    (and (natp n) (<= n (nfix (- (nfix extent) (fn-lgdm-q ps)))) n)))

; One probe step: H the header window read at Q, E the entry fn-lgdm-entry-len
; named read at Q (or NIL).  A valid entry is counted (its records too, from
; the same frame open, fn-lgw-decide) and stepped over; anything else advances
; one unit.
(defun fn-lgdm-step (h e ps unit max)
  (declare (xargs :guard (true-listp ps)))
  (let ((q (fn-lgdm-q ps)) (first (fn-lgdm-first ps)))
    (mv-let (ok records) (fn-lgw-decide e (ec-call (fn-lgs-claimed-prev e max)) max)
      (if ok
          (let* ((n (len e)) (step (+ n (fn-lg-pad-len n unit))))
            (fn-lgdm-make (+ q step) (if first first q) (1+ (fn-lgdm-entries ps))
                          (+ (fn-lgdm-records ps) (len records)) (fn-lgdm-debris ps)))
        (fn-lgdm-make (+ q (fn-lgdm-stride unit)) first (fn-lgdm-entries ps)
                      (fn-lgdm-records ps)
                      (+ (fn-lgdm-debris ps) (if (fn-lgdm-nonzero-p h) 1 0)))))))

; The verdict from the stream's stopped state ST and the probe's final state.
(defun fn-lgdm-verdict (st ps extent)
  (declare (xargs :guard (and (true-listp st) (true-listp ps))))
  (let ((p (fn-lgw-pos st)))
    (cond ((fn-lgw-broken st) (list :broken p))
          ((fn-lgdm-first ps)
           (list :damaged p (nfix (fn-lgdm-first ps)) (fn-lgdm-entries ps) (fn-lgdm-records ps)))
          ((and (< p (nfix extent)) (< 0 (fn-lgdm-debris ps)))
           (list :torn p (fn-lgdm-debris ps)))
          (t (list :complete p)))))

(defun fn-lgdm-refused-p (v)
  (declare (xargs :guard t))
  (and (consp v) (member-eq (car v) '(:broken :damaged)) t))

; -----------------------------------------------------------------------------
; The lines ACL2 owns.

(defthm fn-lgdm-characterp-of-digit-char
  (characterp (fn-lgs-digit-char d))
  :rule-classes :type-prescription)

(defun fn-lgdm-dec-chars (n acc)
  (declare (xargs :guard (and (natp n) (character-listp acc)) :measure (nfix n)))
  (if (zp n)
      acc
    (fn-lgdm-dec-chars (floor n 10) (cons (fn-lgs-digit-char (mod n 10)) acc))))

(defthm fn-lgdm-character-listp-of-dec-chars
  (implies (character-listp acc) (character-listp (fn-lgdm-dec-chars n acc))))

(defun fn-lgdm-dec (n)
  (declare (xargs :guard t))
  (let ((n (nfix n))) (if (zp n) "0" (coerce (fn-lgdm-dec-chars n nil) 'string))))

(defun fn-lgdm-at (segment p)
  (declare (xargs :guard t))
  (concatenate 'string (if (stringp segment) segment "?") ":" (fn-lgdm-dec p)))

; The refusal line of a refused verdict (NIL for one that is not refused).
(defun fn-lgdm-refusal-text (v segment)
  (declare (xargs :guard t))
  (cond ((not (and (consp v) (true-listp v))) nil)
        ((equal (car v) :damaged)
         (concatenate 'string
                      "open refused reason=log-damaged at=" (fn-lgdm-at segment (nth 1 v))
                      " first-valid=" (fn-lgdm-dec (nth 2 v))
                      " valid-after=" (fn-lgdm-dec (nth 3 v))
                      " records=" (fn-lgdm-dec (nth 4 v))
                      ": an entry of the record log does not validate and valid entries follow it"
                      " (damage, not a torn tail); nothing was written.  To keep the history before"
                      " it and drop the rest (the segment is kept under quarantine/ first):"
                      " recover --repair truncate "
                      (fn-lgdm-at segment (nth 1 v))))
        ((equal (car v) :broken)
         (concatenate 'string
                      "open refused reason=log-chain-broken at=" (fn-lgdm-at segment (nth 1 v))
                      ": a log segment holds an entry chained from another history"))
        (t nil)))

; The report line of a torn tail the open dropped (NIL otherwise).
(defun fn-lgdm-report-text (v segment)
  (declare (xargs :guard t))
  (and (consp v) (true-listp v) (equal (car v) :torn)
       (concatenate 'string "log torn-tail at=" (fn-lgdm-at segment (nth 1 v))
                    " debris-units=" (fn-lgdm-dec (nth 2 v))
                    " (dropped: the incomplete last write)")))

; The operator's confirmed repair: admitted only for the :damaged verdict of
; exactly this segment at exactly this offset, in a writable open of the
; ACTIVE segment (WRITABLE): a closed segment's damage is not truncated here,
; since the segments after it chain from its last entry.
(defun fn-lgdm-repair-admitsp (v segment confirm writable)
  (declare (xargs :guard t))
  (and writable
       (consp v) (true-listp v) (equal (car v) :damaged)
       (stringp confirm)
       (equal confirm (fn-lgdm-at segment (nth 1 v)))
       t))

; The verdict the open proceeds on: a confirmed repair of this damage
; recovers to the stop; everything else is the verdict itself.
(defun fn-lgdm-effective (v segment confirm writable)
  (declare (xargs :guard t))
  (if (fn-lgdm-repair-admitsp v segment confirm writable)
      (list :repaired (nth 1 v) (nth 3 v) (nth 4 v))
    v))

; Where the host keeps the damaged segment's octets before the repair's
; truncation (under the store's quarantine/ directory).
(defun fn-lgdm-quarantine-name (v segment)
  (declare (xargs :guard t))
  (and (consp v) (true-listp v) (equal (car v) :repaired)
       (concatenate 'string (if (stringp segment) segment "segment")
                    ".damaged-at-" (fn-lgdm-dec (nth 1 v)))))

(defun fn-lgdm-repair-text (v segment)
  (declare (xargs :guard t))
  (and (consp v) (true-listp v) (equal (car v) :repaired)
       (concatenate 'string "log repaired at=" (fn-lgdm-at segment (nth 1 v))
                    " dropped-valid-entries=" (fn-lgdm-dec (nth 2 v))
                    " dropped-records=" (fn-lgdm-dec (nth 3 v))
                    " (the operator's truncate: the damaged entry and every entry after it;"
                    " the segment's octets were kept first)")))

; -----------------------------------------------------------------------------
; The host's loop over the segment's octets C.

(defun fn-lgdm-hwindow (c ps)
  (declare (xargs :guard (true-listp ps) :verify-guards nil))
  (fn-bs-take (fn-lgdm-header-len ps (len c)) (nthcdr (fn-lgdm-q ps) c)))

(defun fn-lgdm-window (c ps)
  (declare (xargs :guard (true-listp ps) :verify-guards nil))
  (let ((n (fn-lgdm-entry-len (fn-lgdm-hwindow c ps) ps (len c))))
    (and n (fn-bs-take n (nthcdr (fn-lgdm-q ps) c)))))

(defthm fn-lgdm-decide-ok-is-valid
  (equal (mv-nth 0 (fn-lgw-decide e (fn-lgs-claimed-prev e max) max))
         (fn-lgdm-valid-p e max))
  :hints (("Goal" :in-theory (disable fn-lgw-decide fn-lg-entry-okp fn-lgs-claimed-prev)
           :use ((:instance fn-lgw-decide-is-okp-and-records
                            (prev (fn-lgs-claimed-prev e max)))))))

(defthm fn-lgdm-valid-len
  (implies (fn-lgdm-valid-p e max) (< 0 (len e)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-lg-entry-okp fn-lgs-claimed-prev))))

(defthm fn-lgdm-step-q-grows
  (< (fn-lgdm-q ps) (fn-lgdm-q (fn-lgdm-step h e ps unit max)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-lgw-decide fn-lgs-claimed-prev fn-lg-pad-len
                                      fn-lgdm-valid-p fn-lgdm-nonzero-p))))

(defun fn-lgdm-run (c ps unit max)
  (declare (xargs :measure (nfix (- (len c) (fn-lgdm-q ps)))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-lgdm-step fn-lgdm-window fn-lgdm-hwindow)))))
  (if (<= (len c) (fn-lgdm-q ps))
      ps
    (fn-lgdm-run c (fn-lgdm-step (fn-lgdm-hwindow c ps) (fn-lgdm-window c ps) ps unit max)
                 unit max)))

; -----------------------------------------------------------------------------
; The specification: the least unit-aligned offset at or past Q where a valid
; entry starts.

(defun fn-lgdm-least-valid (c q unit max)
  (declare (xargs :measure (nfix (- (len c) (nfix q))) :verify-guards nil))
  (let ((q (nfix q)))
    (cond ((<= (len c) q) nil)
          ((fn-lgdm-valid-p (fn-lg-slice (nthcdr q c)) max) q)
          (t (fn-lgdm-least-valid c (+ q (fn-lgdm-stride unit)) unit max)))))

(local
 (defthm fn-lgdm-len-nthcdr
  (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))))

(defthm fn-lgdm-window-is-the-slice
  (implies (<= (fn-lgdm-q ps) (len c))
           (equal (fn-lgdm-window c ps)
                  (fn-lg-slice (nthcdr (fn-lgdm-q ps) c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-declared-len fn-lg-slice fn-lgd-declared-len-of-header)
           :use ((:instance fn-lgd-declared-len-of-header (x (nthcdr (fn-lgdm-q ps) c)))))))

(defthm fn-lgdm-first-of-step
  (equal (fn-lgdm-first (fn-lgdm-step h e ps unit max))
         (if (fn-lgdm-first ps) (fn-lgdm-first ps) (if (fn-lgdm-valid-p e max) (fn-lgdm-q ps) nil)))
  :hints (("Goal" :cases ((fn-lgdm-valid-p e max))
           :in-theory (disable fn-lgw-decide fn-lgs-claimed-prev fn-lgdm-valid-p fn-lg-pad-len
                               fn-lgdm-nonzero-p))))

(defthm fn-lgdm-step-when-not-valid
  (implies (not (fn-lgdm-valid-p e max))
           (equal (fn-lgdm-q (fn-lgdm-step h e ps unit max))
                  (+ (fn-lgdm-q ps) (fn-lgdm-stride unit))))
  :hints (("Goal" :in-theory (disable fn-lgw-decide fn-lgs-claimed-prev fn-lgdm-valid-p
                                      fn-lgdm-nonzero-p fn-lgdm-stride))))

(in-theory (disable fn-lgdm-step))

(defthm fn-lgdm-run-keeps-first
  (implies (fn-lgdm-first ps)
           (equal (fn-lgdm-first (fn-lgdm-run c ps unit max)) (fn-lgdm-first ps)))
  :hints (("Goal" :induct (fn-lgdm-run c ps unit max)
           :in-theory (disable fn-lgdm-window fn-lgdm-hwindow fn-lgdm-valid-p))))

(defthm fn-lgdm-run-first-is-the-least-valid
  (equal (fn-lgdm-first (fn-lgdm-run c ps unit max))
         (or (fn-lgdm-first ps) (fn-lgdm-least-valid c (fn-lgdm-q ps) unit max)))
  :hints (("Goal" :induct (fn-lgdm-run c ps unit max)
           :expand ((fn-lgdm-least-valid c (fn-lgdm-q ps) unit max))
           :in-theory (disable fn-lgdm-window fn-lgdm-hwindow fn-lgdm-valid-p fn-lg-slice
                               fn-lgdm-stride))))

;; Any valid entry on the stride at or past Q is found: the least is no later.
(defthm fn-lgdm-least-valid-when-valid
  (implies (and (natp q) (< q (len c)) (fn-lgdm-valid-p (fn-lg-slice (nthcdr q c)) max))
           (equal (fn-lgdm-least-valid c q unit max) q))
  :hints (("Goal" :expand ((fn-lgdm-least-valid c q unit max))
           :in-theory (disable fn-lgdm-valid-p fn-lg-slice))))

(defthm fn-lgdm-least-valid-when-not-valid
  (implies (and (natp q) (< q (len c)) (not (fn-lgdm-valid-p (fn-lg-slice (nthcdr q c)) max)))
           (equal (fn-lgdm-least-valid c q unit max)
                  (fn-lgdm-least-valid c (+ q (fn-lgdm-stride unit)) unit max)))
  :hints (("Goal" :expand ((fn-lgdm-least-valid c q unit max))
           :in-theory (disable fn-lgdm-valid-p fn-lg-slice fn-lgdm-stride))))

; The least valid offset is a valid entry at or past Q, on Q's stride.
(defthm fn-lgdm-least-valid-past-end
  (implies (<= (len c) (nfix q)) (not (fn-lgdm-least-valid c q unit max)))
  :hints (("Goal" :expand ((fn-lgdm-least-valid c q unit max)))))

(defthm fn-lgdm-least-valid-is-valid
  (implies (natp q)
           (let ((f (fn-lgdm-least-valid c q unit max)))
             (implies f
                      (and (natp f)
                           (<= q f)
                           (< f (len c))
                           (fn-lgdm-valid-p (fn-lg-slice (nthcdr f c)) max)))))
  :hints (("Goal" :induct (fn-lgdm-least-valid c q unit max)
           :in-theory (disable fn-lgdm-valid-p fn-lg-slice fn-lgdm-stride
                               (:definition fn-lgdm-least-valid) fn-lgc-multiple-minus-unit))))

(defun fn-lgdm-witness-ind (q k unit)
  (declare (xargs :measure (nfix k)))
  (if (zp k) q (fn-lgdm-witness-ind (+ (nfix q) (fn-lgdm-stride unit)) (1- k) unit)))

(defthm fn-lgdm-least-valid-finds-any-witness
  (implies (and (natp k) (natp q)
                (equal w (+ q (* k (fn-lgdm-stride unit))))
                (< w (len c))
                (fn-lgdm-valid-p (fn-lg-slice (nthcdr w c)) max))
           (and (fn-lgdm-least-valid c q unit max)
                (<= (fn-lgdm-least-valid c q unit max) w)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-lgdm-witness-ind q k unit)
           :in-theory (disable fn-lgdm-valid-p fn-lg-slice fn-lgdm-stride fn-lgdm-least-valid
                               fn-lgc-multiple-minus-unit))
          ("Subgoal *1/2" :cases ((fn-lgdm-valid-p (fn-lg-slice (nthcdr q c)) max)))))

; -----------------------------------------------------------------------------
; KEYSTONES over the host's composition: the stream's run (the open's
; records and kernel, fn-lgw-run-is-the-open), then the probe from its stop,
; then the verdict.

(defun fn-lgdm-open (c genesis floor unit max)
  (declare (xargs :verify-guards nil))
  (mv-let (records st) (fn-lgw-run c (fn-lgw-start genesis floor) unit max)
    (declare (ignore records))
    (fn-lgdm-verdict st (fn-lgdm-run c (fn-lgdm-start st) unit max) (len c))))

; The specification: the scan's stop, the splice verdict, and the least valid
; entry at or past the stop.
(defun fn-lgdm-classify (c genesis unit max)
  (declare (xargs :verify-guards nil))
  (let* ((p (cdr (fn-lg-scan c genesis unit max)))
         (f (fn-lgdm-least-valid c p unit max)))
    (cond ((fn-lgs-chain-broken-p c genesis unit max) (list :broken p))
          (f (list :damaged p f))
          (t (list :intact p)))))

(defun fn-lgdm-kind (v)
  (declare (xargs :guard t))
  (if (consp v) (if (member-eq (car v) '(:torn :complete)) :intact (car v)) nil))

(defthm fn-lgdm-stream-stop
  (let ((st (mv-nth 1 (fn-lgw-run c (fn-lgw-start genesis floor) unit max))))
    (and (equal (fn-lgw-pos st) (cdr (fn-lg-scan c genesis unit max)))
         (equal (fn-lgw-broken st) (fn-lgs-chain-broken-p c genesis unit max))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgw-run fn-lg-scan fn-lg-scan-last fn-lgs-chain-broken-p
                               fn-lgw-run-is-the-scan fn-lgw-run-is-the-open fn-lgt-next-after)
           :use ((:instance fn-lgw-run-is-the-scan (st (fn-lgw-start genesis floor)))))))

; The shapes of the verdict and of the classification.
(defthm fn-lgdm-verdict-shape
  (let ((v (fn-lgdm-verdict st ps extent)))
    (and (equal (nth 1 v) (fn-lgw-pos st))
         (equal (fn-lgdm-kind v)
                (cond ((fn-lgw-broken st) :broken)
                      ((fn-lgdm-first ps) :damaged)
                      (t :intact)))
         (equal (fn-lgdm-refused-p v)
                (if (or (fn-lgw-broken st) (fn-lgdm-first ps)) t nil))
         (equal (equal (car v) :damaged)
                (if (and (not (fn-lgw-broken st)) (fn-lgdm-first ps)) t nil))
         (implies (equal (car v) :damaged)
                  (equal (nth 2 v) (nfix (fn-lgdm-first ps)))))))

(defthm fn-lgdm-classify-shape
  (let ((s (fn-lgdm-classify c genesis unit max))
        (p (cdr (fn-lg-scan c genesis unit max))))
    (and (equal (nth 1 s) p)
         (equal (car s)
                (cond ((fn-lgs-chain-broken-p c genesis unit max) :broken)
                      ((fn-lgdm-least-valid c p unit max) :damaged)
                      (t :intact)))
         (implies (equal (car s) :damaged)
                  (equal (nth 2 s) (fn-lgdm-least-valid c p unit max)))))
  :hints (("Goal" :in-theory (disable fn-lg-scan fn-lgs-chain-broken-p fn-lgdm-least-valid))))

(in-theory (disable fn-lgdm-verdict fn-lgdm-classify fn-lgdm-kind fn-lgdm-refused-p))

(defthm fn-lgdm-open-verdict-is-the-classification
  (let ((v (fn-lgdm-open c genesis floor unit max))
        (s (fn-lgdm-classify c genesis unit max)))
    (and (equal (fn-lgdm-kind v) (car s))
         (equal (nth 1 v) (nth 1 s))
         (implies (equal (car v) :damaged) (equal (nth 2 v) (nth 2 s)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgw-run fn-lgdm-run fn-lg-scan fn-lg-scan-last fn-lgs-chain-broken-p
                               fn-lgdm-least-valid fn-lgw-run-is-the-scan fn-lgw-run-is-the-open
                               fn-lgt-next-after fn-lgw-start))))

(defthm fn-lgdm-classify-refuses-any-witness
  (implies (and (natp k)
                (< (+ (cdr (fn-lg-scan c genesis unit max)) (* k (fn-lgdm-stride unit))) (len c))
                (fn-lgdm-valid-p (fn-lg-slice (nthcdr (+ (cdr (fn-lg-scan c genesis unit max))
                                                         (* k (fn-lgdm-stride unit)))
                                                      c))
                                 max))
           (member-equal (car (fn-lgdm-classify c genesis unit max)) '(:broken :damaged)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-scan fn-lgs-chain-broken-p fn-lgdm-least-valid fn-lgdm-valid-p
                               fn-lg-slice fn-lgdm-stride)
           :use ((:instance fn-lgdm-least-valid-finds-any-witness
                            (q (cdr (fn-lg-scan c genesis unit max)))
                            (w (+ (cdr (fn-lg-scan c genesis unit max)) (* k (fn-lgdm-stride unit)))))))))

(defthm fn-lgdm-classify-damaged-names-a-valid-entry
  (let ((s (fn-lgdm-classify c genesis unit max)))
    (implies (equal (car s) :damaged)
             (and (natp (nth 2 s))
                  (<= (nth 1 s) (nth 2 s))
                  (< (nth 2 s) (len c))
                  (fn-lgdm-valid-p (fn-lg-slice (nthcdr (nth 2 s) c)) max))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-scan fn-lgs-chain-broken-p fn-lgdm-least-valid fn-lgdm-valid-p
                               fn-lg-slice fn-lgdm-stride fn-lgdm-least-valid-is-valid)
           :use ((:instance fn-lgdm-least-valid-is-valid (q (cdr (fn-lg-scan c genesis unit max))))))))

(in-theory (disable fn-lgdm-open))

(defthm fn-lgdm-refused-p-by-kind
  (equal (fn-lgdm-refused-p v) (if (member-equal (fn-lgdm-kind v) '(:broken :damaged)) t nil))
  :hints (("Goal" :in-theory (enable fn-lgdm-refused-p fn-lgdm-kind))))

(defthm fn-lgdm-damaged-by-kind
  (and (equal (equal (car v) :damaged) (equal (fn-lgdm-kind v) :damaged))
       (equal (equal (car v) :broken) (equal (fn-lgdm-kind v) :broken)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-lgdm-kind))))

(defthm fn-lgdm-no-silent-prefix
  (let* ((v (fn-lgdm-open c genesis floor unit max))
         (p (nth 1 v)))
    (and (equal p (cdr (fn-lg-scan c genesis unit max)))
         (implies (and (natp k)
                       (< (+ p (* k (fn-lgdm-stride unit))) (len c))
                       (fn-lgdm-valid-p (fn-lg-slice (nthcdr (+ p (* k (fn-lgdm-stride unit))) c))
                                        max))
                  (fn-lgdm-refused-p v))
         (implies (equal (car v) :damaged)
                  (and (<= p (nth 2 v))
                       (< (nth 2 v) (len c))
                       (fn-lgdm-valid-p (fn-lg-slice (nthcdr (nth 2 v) c)) max)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lgdm-refused-p-by-kind member-equal)
                                      (theory 'minimal-theory))
           :use ((:instance fn-lgdm-open-verdict-is-the-classification)
                 (:instance fn-lgdm-damaged-by-kind (v (fn-lgdm-open c genesis floor unit max)))
                 (:instance fn-lgdm-classify-refuses-any-witness)
                 (:instance fn-lgdm-classify-damaged-names-a-valid-entry)
                 (:instance fn-lgdm-classify-shape)))))

; -----------------------------------------------------------------------------
; KEYSTONE: after a well-formed log, damage lies in what follows it.

(local
 (defun fn-lgdm-zeros-ind (n z)
   (if (or (zp n) (zp z)) (list n z) (fn-lgdm-zeros-ind (1- n) (1- z)))))

(local
 (defthm fn-lgdm-nthcdr-of-zeros-starts-with-zero
   (or (atom (nthcdr n (fn-bs-zeros z)))
       (equal (car (nthcdr n (fn-bs-zeros z))) 0))
   :rule-classes nil
   :hints (("Goal" :induct (fn-lgdm-zeros-ind n z) :expand ((fn-bs-zeros z))
            :in-theory (enable fn-bs-zeros)))))

(local
 (defthm fn-lgdm-slice-of-zero
   (implies (or (atom x) (equal (car x) 0)) (not (fn-lg-slice x)))
   :hints (("Goal" :in-theory (enable fn-lg-slice fn-lg-declared-len fn-bs-take)))))

(local
 (defthm fn-lgdm-no-slice-in-zeros
   (not (fn-lg-slice (nthcdr n (fn-bs-zeros z))))
   :hints (("Goal" :in-theory (disable fn-lg-slice)
            :use ((:instance fn-lgdm-nthcdr-of-zeros-starts-with-zero)
                  (:instance fn-lgdm-slice-of-zero (x (nthcdr n (fn-bs-zeros z)))))))))

(local
 (defthm fn-lgdm-nthcdr-of-append-past
   (implies (and (natp q) (<= (len a) q))
            (equal (nthcdr q (append a b)) (nthcdr (- q (len a)) b)))
   :hints (("Goal" :induct (nthcdr q a)))))

(defthm fn-lgdm-not-valid-nil
  (not (fn-lgdm-valid-p nil max))
  :hints (("Goal" :in-theory (enable fn-lg-entry-okp))))

(defthm fn-lgdm-no-valid-entry-in-zeros
  (implies (and (natp q) (<= (+ (len a) (len y)) q))
           (not (fn-lgdm-valid-p (fn-lg-slice (nthcdr q (append a y (fn-bs-zeros z)))) max)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-slice fn-lgdm-valid-p fn-lgdm-nthcdr-of-append-past)
           :use ((:instance fn-lgdm-nthcdr-of-append-past (b (append y (fn-bs-zeros z))))
                 (:instance fn-lgdm-nthcdr-of-append-past (a y) (b (fn-bs-zeros z))
                            (q (- q (len a))))
                 (:instance fn-lgdm-no-slice-in-zeros (n (- (- q (len a)) (len y))))))))

(defthm fn-lgdm-broken-is-valid-at-the-stop
  (implies (fn-lgs-chain-broken-p c genesis unit max)
           (fn-lgdm-valid-p (fn-lg-slice (nthcdr (cdr (fn-lg-scan c genesis unit max)) c)) max))
  :hints (("Goal" :in-theory (disable fn-lg-scan fn-lg-scan-last fn-lg-slice fn-lg-entry-okp
                                      fn-lgs-claimed-prev))))

(defthm fn-lgdm-classify-refusal-lies-in-y
  (implies (and (natp z) (equal c (append a y (fn-bs-zeros z))))
           (let ((s (fn-lgdm-classify c genesis unit max)))
             (and (implies (equal (car s) :damaged) (< (nth 2 s) (+ (len a) (len y))))
                  (implies (equal (car s) :broken) (< (nth 1 s) (+ (len a) (len y)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-lg-scan-consumed-natp (octets c) (prev genesis))
                 (:instance fn-lgdm-classify-damaged-names-a-valid-entry)
                 (:instance fn-lgdm-classify-shape)
                 (:instance fn-lgdm-broken-is-valid-at-the-stop)
                 (:instance fn-lgdm-no-valid-entry-in-zeros
                            (q (nth 2 (fn-lgdm-classify c genesis unit max))))
                 (:instance fn-lgdm-no-valid-entry-in-zeros
                            (q (cdr (fn-lg-scan c genesis unit max))))))))

(defthm fn-lgdm-stop-past-the-log
  (implies (and (fn-frame-digestp genesis) (fn-lg-recordsp records max))
           (<= (len (fn-lg-log records genesis unit))
               (cdr (fn-lg-scan (append (fn-lg-log records genesis unit) x) genesis unit max))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-scan fn-lg-log fn-lg-scan-of-log-append fn-lgc-log-len-is-the-log-length)
           :use ((:instance fn-lg-scan-of-log-append (prev genesis))))))

(defthm fn-lgdm-open-refusal-lies-in-y
  (implies (and (natp z) (equal c (append a y (fn-bs-zeros z)))
                (<= (len a) (cdr (fn-lg-scan c genesis unit max))))
           (let ((v (fn-lgdm-open c genesis floor unit max)))
             (and (<= (len a) (nth 1 v))
                  (implies (equal (car v) :damaged)
                           (and (<= (len a) (nth 2 v)) (< (nth 2 v) (+ (len a) (len y)))))
                  (implies (equal (car v) :broken) (< (nth 1 v) (+ (len a) (len y))))
                  (implies (atom y) (not (fn-lgdm-refused-p v))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lgdm-refused-p-by-kind member-equal len)
                                      (theory 'minimal-theory))
           :use ((:instance fn-lgdm-open-verdict-is-the-classification)
                 (:instance fn-lgdm-damaged-by-kind (v (fn-lgdm-open c genesis floor unit max)))
                 (:instance fn-lgdm-classify-shape)
                 (:instance fn-lgdm-classify-damaged-names-a-valid-entry)
                 (:instance fn-lgdm-classify-refusal-lies-in-y)))))

(defthm fn-lgdm-damage-lies-in-the-last-write
  (implies (and (fn-frame-digestp genesis) (fn-lg-recordsp records max) (natp z)
                (equal c (append (fn-lg-log records genesis unit) y (fn-bs-zeros z))))
           (let ((v (fn-lgdm-open c genesis floor unit max))
                 (l (len (fn-lg-log records genesis unit))))
             (and (<= l (nth 1 v))
                  (implies (equal (car v) :damaged)
                           (and (<= l (nth 2 v)) (< (nth 2 v) (+ l (len y)))))
                  (implies (equal (car v) :broken) (< (nth 1 v) (+ l (len y))))
                  (implies (atom y) (not (fn-lgdm-refused-p v))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-lgdm-open-refusal-lies-in-y (a (fn-lg-log records genesis unit)))
                 (:instance fn-lgdm-stop-past-the-log (x (append y (fn-bs-zeros z))))))))

; The repair changes nothing but the confirmed damage of the active segment in
; a writable open, and it keeps the stop (the recovered prefix is the scan's).
(defthm fn-lgdm-repair-is-only-the-confirmed-damage
  (let ((e (fn-lgdm-effective v segment confirm writable)))
    (and (implies (not (fn-lgdm-repair-admitsp v segment confirm writable))
                  (equal e v))
         (implies (fn-lgdm-repair-admitsp v segment confirm writable)
                  (and writable
                       (equal (car v) :damaged)
                       (equal confirm (fn-lgdm-at segment (nth 1 v)))
                       (equal (car e) :repaired)
                       (equal (nth 1 e) (nth 1 v))
                       (not (fn-lgdm-refused-p e))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-lgdm-refused-p fn-lgdm-kind))))

; -----------------------------------------------------------------------------
; The history read again (host/native/io.lisp fnn-log-history-each and
; fnn-log-closed-records: checkpoint publish, export): the closed segments are
; streamed again with the chain carried from one to the next, and the last
; closed segment's last trailer must be the active segment's genesis.  A
; closed segment that changed since the open (read shorter, or damaged at its
; last entry, which no probe can tell from a torn tail) breaks it: refused by
; name, never a shorter history handed to a checkpoint that then drops the
; covered segments.

(defun fn-lgdm-chain-continues-p (last genesis)
  (declare (xargs :guard t))
  (equal last genesis))

(defun fn-lgdm-history-break-text ()
  (declare (xargs :guard t))
  "history refused reason=log-damaged: the closed log segments read again do not chain to the active segment's genesis (a closed segment changed since the open); nothing was written")
