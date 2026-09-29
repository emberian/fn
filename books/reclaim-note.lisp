; fn: what a reclaim decided, recorded beside its instant (PKT-855, N2 of
; lane proto-determinism; planning/design-reclaim-note-2026-09-29.md).
;
; `store reclaim' rewrites every article record its context releases into
; the record's tombstone (books/store-log-reclaim.lisp) and drops the
; segments the rewritten history's checkpoint covers.  PKT-857
; (books/reclaim-instant.lisp) records the instant the context read, so a
; holder of the pre-reclaim history can re-derive the decision
; (fn-rci-recorded-decision-is-the-decision).  What it could not do is CHECK
; it, or place it: nothing durable said which history the reclaim decided
; over or what it reclaimed.
;
; The note is a configuration delta (books/config.lisp fn-cfg-reclaim-note,
; code 28) published in the SAME record as the instant, so the two are one
; publication: no process death separates them.  Its text is ACL2's summary
; of the decision:
;
;   at=CODE history=N reclaimed=K freed=F msgids=HEX
;
; CODE the instant's row value (fn-rci-code), N the pre-reclaim history's
; record count, K and F the decision's reclaimed count and freed octets, HEX
; the SHA-256 of the reclaimed Message-IDs in history order, each preceded by
; its length as a big-endian u32.  A holder of the pre-reclaim history and the
; configuration record recomputes the decision `--recorded' and compares
; texts; `store reclaim --recorded' does exactly that before it rewrites
; (fn-rcn-check, called by host/checkpoint-host.lisp
; fn-store-reclaim-note-check).
;
; KEYSTONES:
;   fn-rcn-recorded-note-reads-back: the record's configuration carries the
;     instant, the rule and the note text unchanged;
;   fn-rcn-recorded-note-checks: over that configuration, the --recorded
;     rerun's decision (fn-rci-decide-stream) checks :checked against the note the
;     host published from its own decision at the clock -- the reachable
;     positive case, the rerun after a process death between the record and
;     the checkpoint's install.
(in-package "ACL2")
(include-book "reclaim-instant")
(include-book "sha256")
(local (include-book "arithmetic/top" :dir :system)) ; fn-rcn-dec-chars' measure

; -----------------------------------------------------------------------------
; The text.

(defun fn-rcn-hex-digit (d)
  (declare (xargs :guard t))
  (let ((d (nfix d)))
    (if (< d 10) (code-char (+ 48 d)) (code-char (+ 87 (min d 15))))))

(defun fn-rcn-dec-chars (n acc)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (< n 10)
        (cons (fn-rcn-hex-digit n) acc)
      (fn-rcn-dec-chars (floor n 10) (cons (fn-rcn-hex-digit (mod n 10)) acc)))))

(defthm fn-rcn-characterp-of-hex-digit
  (characterp (fn-rcn-hex-digit d)))

(defthm fn-rcn-character-listp-of-dec-chars
  (implies (character-listp acc)
           (character-listp (fn-rcn-dec-chars n acc)))
  :hints (("Goal" :in-theory (disable fn-rcn-hex-digit))))

(defun fn-rcn-dec (n)
  (declare (xargs :guard t))
  (coerce (fn-rcn-dec-chars n nil) 'string))

(defun fn-rcn-hex-chars (octets)
  (declare (xargs :guard t))
  (if (consp octets)
      (let ((o (nfix (car octets))))
        (list* (fn-rcn-hex-digit (floor (mod o 256) 16))
               (fn-rcn-hex-digit (mod o 16))
               (fn-rcn-hex-chars (cdr octets))))
    nil))

(defthm fn-rcn-character-listp-of-hex-chars
  (character-listp (fn-rcn-hex-chars octets))
  :hints (("Goal" :in-theory (disable fn-rcn-hex-digit))))

(defun fn-rcn-hex (octets)
  (declare (xargs :guard t))
  (coerce (fn-rcn-hex-chars octets) 'string))

(defun fn-rcn-u32 (n)
  (declare (xargs :guard t))
  (let ((n (nfix n)))
    (list (mod (floor n 16777216) 256) (mod (floor n 65536) 256)
          (mod (floor n 256) 256) (mod n 256))))

; Each Message-ID's octets preceded by their count (a u32: a Message-ID is
; far shorter, books/records-shape.lisp; an unrepresentable length never
; arises, and the prefix would still be exact modulo 2^32).
(defun fn-rcn-msgids-octets (msgids)
  (declare (xargs :guard t))
  (if (consp msgids)
      (let ((o (fn-record-string-octets (car msgids))))
        (append (fn-rcn-u32 (len o)) o (fn-rcn-msgids-octets (cdr msgids))))
    nil))

; The note's instant prefix: "at=CODE ".
(defun fn-rcn-at-prefix (code)
  (declare (xargs :guard t))
  (concatenate 'string "at=" (fn-rcn-dec code) " "))

(defun fn-rcn-text (code count msgids freed)
  (declare (xargs :guard t))
  (concatenate 'string
               (fn-rcn-at-prefix code)
               "history=" (fn-rcn-dec count)
               " reclaimed=" (fn-rcn-dec (len msgids))
               " freed=" (fn-rcn-dec freed)
               " msgids=" (fn-rcn-hex (fn-sha256 (fn-rcn-msgids-octets msgids)))))

; The note of a decision (fn-lgr-decide-stream's or fn-rci-decide-stream's
; (:reclaim MSGIDS FREED COUNTS)) at NOW over a history of COUNT records.
(defun fn-rcn-of-decision (now count d)
  (declare (xargs :guard t))
  (if (and (consp d) (equal (car d) :reclaim))
      (fn-rcn-text (fn-rci-code now) count (fn-rcl-nth 1 d) (fn-rcl-nth 2 d))
    ""))

; The note is publishable: a non-empty configuration label.
(defun fn-rcn-representablep (text)
  (declare (xargs :guard t))
  (and (fn-cfg-labelp text) (consp (fn-record-string-octets text))))

; The record's two deltas: the instant (PKT-857's, unchanged) then the note.
(defun fn-rcn-deltas (now text)
  (declare (xargs :guard t))
  (list (fn-rci-delta now) (fn-cfg-reclaim-note text)))

; The configuration value's latest note ("" when none).
(defun fn-rcn-config-note (v)
  (declare (xargs :guard t))
  (let ((row (fn-rcl-limit-row (fn-cfg-limits v) *fn-cfg-reclaim-note-slot*)))
    (if row (fn-cfg-row-c row) "")))

(defun fn-rcn-prefixp (p text)
  (declare (xargs :guard t))
  (let ((p (if (stringp p) (coerce p 'list) nil))
        (x (if (stringp text) (coerce text 'list) nil)))
    (and (<= (len p) (len x))
         (equal (take (len p) x) p))))

; `store reclaim --recorded''s check of its decision D over COUNT records
; against the configuration V it opened with: :checked when the note written
; at the recorded instant is D's note, :reclaim-note-mismatch when it is not
; (the rerun refuses by name and rewrites nothing), :unchecked when D
; reclaims nothing or the configuration's note is of an earlier instant (the
; live pass records its instant without a note: books/owner-reclaim-
; instant.lisp).
(defun fn-rcn-check (v count d)
  (declare (xargs :guard t))
  (let ((note (fn-rcn-config-note v))
        (code (fn-rci-code (fn-rci-config-now v))))
    (cond ((not (and (consp d) (equal (car d) :reclaim))) :unchecked)
          ((not (fn-rcn-prefixp (fn-rcn-at-prefix code) note)) :unchecked)
          ((equal note (fn-rcn-of-decision (fn-rci-config-now v) count d)) :checked)
          (t :reclaim-note-mismatch))))

; The configuration the published record yields (host/checkpoint-host.lisp
; fn-store-reclaim-instant-record over fn-rcn-deltas).
(defun fn-rcn-recorded-config (cfg q tx g stamp now text)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cfg-apply-record cfg (fn-cfg-record-make q tx g (fn-rcn-deltas now text) stamp)))

; -----------------------------------------------------------------------------
; Lookup after the rows' upserts.

(local
 (defthm fn-rcn-limit-row-of-upsert-same
   (implies (and (equal (fn-cfg-row-a row) slot)
                 (equal (fn-cfg-row-b row) ""))
            (equal (fn-rcl-limit-row (fn-cfg-row-upsert rows row) slot) row))
   :hints (("Goal" :induct (fn-cfg-row-upsert rows row)
            :in-theory (enable fn-cfg-row-upsert)))))

(local
 (defthm fn-rcn-limit-row-of-upsert-other
   (implies (not (equal (fn-cfg-row-a row) slot))
            (equal (fn-rcl-limit-row (fn-cfg-row-upsert rows row) slot)
                   (fn-rcl-limit-row rows slot)))
   :hints (("Goal" :induct (fn-cfg-row-upsert rows row)
            :in-theory (enable fn-cfg-row-upsert)))))

(local
 (defthm fn-rcn-value-of-apply-record
   (equal (fn-cfg-value (fn-cfg-apply-record cfg (fn-cfg-record-make q tx g change stamp)))
          (fn-cfg-apply (fn-cfg-value cfg) g stamp change))
   :hints (("Goal" :in-theory (enable fn-cfg-apply-record fn-cfg-value fn-cfg-make
                                      fn-cfg-ag-car fn-cfg-ag-cdr)))))

(local
 (defthm fn-rcn-limits-of-the-deltas
   (equal (fn-cfg-limits (fn-cfg-apply v g stamp (fn-rcn-deltas now text)))
          (fn-cfg-row-upsert
           (fn-cfg-row-upsert (fn-cfg-limits v)
                              (fn-cfg-row-make *fn-rci-slot* "" "" (fn-rci-code now)))
           (fn-cfg-row-make *fn-cfg-reclaim-note-slot* "" text 0)))
   :hints (("Goal" :in-theory (enable fn-cfg-apply fn-cfg-apply-delta fn-rcn-deltas
                                      fn-rci-delta fn-cfg-set-limit fn-cfg-reclaim-note
                                      fn-cfg-delta-make fn-cfg-delta-kind fn-cfg-delta-a
                                      fn-cfg-delta-b fn-cfg-delta-n fn-cfg-delta-rows
                                      fn-cfg-ag-car fn-cfg-ag-cdr)))))

(local (in-theory (disable fn-cfg-apply-delta fn-cfg-apply fn-cfg-apply-record
                           fn-cfg-limits fn-cfg-row-upsert fn-cfg-value
                           fn-cfg-record-make fn-rcn-deltas (:e fn-rcn-deltas))))

; KEYSTONE.  The record's configuration carries the instant (so every
; theorem of books/reclaim-instant.lisp about the context and the decision
; holds of it), the rule unchanged, and the note text.
(defthm fn-rcn-recorded-note-reads-back
  (implies (fn-rci-instantp now)
           (let ((v (fn-cfg-value (fn-rcn-recorded-config cfg q tx g stamp now text))))
             (and (fn-rci-recordedp v)
                  (equal (fn-rci-config-now v) now)
                  (equal (fn-rcl-config-rule v) (fn-rcl-config-rule (fn-cfg-value cfg)))
                  (equal (fn-rcn-config-note v) text))))
  :hints (("Goal" :in-theory (e/d (fn-rcn-recorded-config fn-rci-recordedp fn-rci-config-now
                                   fn-rci-code fn-rcl-config-rule fn-rcn-config-note
                                   fn-cfg-row-n fn-cfg-row-c fn-cfg-row-make
                                   fn-cfg-row-a fn-cfg-row-b fn-cfg-ag-car fn-cfg-ag-cdr
                                   fn-record-uint32p)
                                  ()))))

; The context and the decision over the record's configuration are the ones
; the host decided under at the clock (as for PKT-857's one-delta record).
(defthm fn-rcn-recorded-decision-is-the-decision
  (implies (fn-rci-instantp now)
           (equal (fn-rci-decide-stream profile
                                        (fn-cfg-value (fn-rcn-recorded-config cfg q tx g stamp now text))
                                        s acc dry fn-arena)
                  (fn-lgr-decide-stream profile (fn-rcl-config-rule (fn-cfg-value cfg)) now
                                        s acc dry fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-rci-decide-stream)
                                  (fn-rcn-recorded-config fn-lgr-decide-stream
                                   fn-rcl-config-rule fn-rci-config-now fn-rci-recordedp))
           :use fn-rcn-recorded-note-reads-back)))

(local
 (defthm fn-rcn-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-rcn-take-len-of-append
   (implies (true-listp a)
            (equal (take (len a) (append a b)) a))))

(local (in-theory (disable string-append)))

(local
 (defthm fn-rcn-prefixp-of-string-append
   (implies (and (stringp p) (stringp r))
            (fn-rcn-prefixp p (string-append p r)))
   :hints (("Goal" :in-theory (enable fn-rcn-prefixp string-append)))))

(local
 (defthm fn-rcn-prefix-of-at-prefix-append
   (fn-rcn-prefixp (fn-rcn-at-prefix code)
                   (fn-rcn-text code count msgids freed))
   :hints (("Goal" :in-theory (e/d (fn-rcn-text) (fn-rcn-at-prefix fn-rcn-prefixp
                                                  fn-rcn-dec fn-rcn-hex string-append))))))

(local
 (defthm fn-rcn-prefix-of-the-decision-note
   (implies (equal (car d) :reclaim)
            (fn-rcn-prefixp (fn-rcn-at-prefix (fn-rci-code now))
                            (fn-rcn-of-decision now count d)))
   :hints (("Goal" :in-theory (e/d (fn-rcn-of-decision)
                                   (fn-rcn-text fn-rcn-at-prefix fn-rcn-prefixp fn-rci-code
                                    (:e fn-rcn-at-prefix) (:e fn-rci-code)))))))

; KEYSTONE.  The --recorded rerun over the record `store reclaim' published
; (the instant and the note of its decision D at the clock, over COUNT
; records) checks the note (:checked whenever D reclaims): the rerun's decision is D (the decision theorem
; above), so its note is the recorded one.
(defthm fn-rcn-recorded-note-checks
  (implies (and (fn-rci-instantp now)
                (equal d (fn-lgr-decide-stream profile (fn-rcl-config-rule (fn-cfg-value cfg))
                                               now s acc nil fn-arena)))
           (let ((v (fn-cfg-value (fn-rcn-recorded-config cfg q tx g stamp now
                                                          (fn-rcn-of-decision now count d)))))
             (equal (fn-rcn-check v count (fn-rci-decide-stream profile v s acc nil fn-arena))
                    (if (equal (car d) :reclaim) :checked :unchecked))))
  :hints (("Goal" :in-theory (e/d (fn-rcn-check)
                                  (fn-rcn-recorded-config fn-lgr-decide-stream fn-rci-decide-stream
                                   fn-rcn-of-decision fn-rcn-config-note fn-rci-config-now
                                   fn-rcn-prefixp fn-rcn-at-prefix fn-rci-code
                                   (:e fn-rcn-at-prefix) (:e fn-rci-code)))
           :use (fn-rcn-recorded-decision-is-the-decision
                 (:instance fn-rcn-recorded-note-reads-back
                            (text (fn-rcn-of-decision now count d)))))))

; A note that is not the decision's, at the recorded instant, is refused.
(defthm fn-rcn-check-refuses-a-foreign-note-by-definition
  (implies (and (consp d) (equal (car d) :reclaim)
                (fn-rcn-prefixp (fn-rcn-at-prefix (fn-rci-code (fn-rci-config-now v)))
                                (fn-rcn-config-note v))
                (not (equal (fn-rcn-config-note v)
                            (fn-rcn-of-decision (fn-rci-config-now v) count d))))
           (equal (fn-rcn-check v count d) :reclaim-note-mismatch))
  :hints (("Goal" :in-theory (e/d (fn-rcn-check)
                                  (fn-rcn-of-decision fn-rcn-config-note fn-rcn-prefixp
                                   fn-rcn-at-prefix fn-rci-code fn-rci-config-now)))))

; The deltas the host stages are configuration deltas.
(defthm fn-rcn-deltas-are-deltas
  (implies (and (fn-rci-representablep now) (fn-rcn-representablep text))
           (fn-cfg-delta-listp (fn-rcn-deltas now text)))
  :hints (("Goal" :in-theory (enable fn-rcn-deltas fn-rci-delta fn-cfg-set-limit
                                     fn-cfg-reclaim-note fn-cfg-delta-make
                                     fn-cfg-deltap fn-cfg-delta-listp fn-cfg-delta-shapep
                                     fn-cfg-delta-kind fn-cfg-delta-a fn-cfg-delta-b
                                     fn-cfg-delta-n fn-cfg-delta-rows fn-cfg-ag-car fn-cfg-ag-cdr
                                     fn-cfg-labelp fn-record-uint32p))))

(in-theory (disable fn-rcn-text fn-rcn-of-decision fn-rcn-check fn-rcn-config-note
                    fn-rcn-recorded-config fn-rcn-deltas))
