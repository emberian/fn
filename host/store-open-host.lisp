; The read-only store open as ACL2 :program code (lane extract-2, 2026-09-28).
;
; Direction (coordinator, 2026-09-28): the host is byte primitives, sockets
; and an event loop; the open sequence belongs in ACL2 so the extractor
; extracts it instead of anyone rewriting host/native by hand.  This file is
; the first pass: the reader's open of a format-9 store over its record log,
; READ-ONLY and by FULL REPLAY (no state checkpoint), as host/native/io.lisp
; does it today in fnn-reader-prepare -> fnn-acquire, fnn-bridge-reset,
; fnn-recover -> fnn-recover-log (the full-replay arm), the recovery barriers,
; fnn-reader-select.  Every decision is the same ACL2 function the image
; calls; what io.lisp did in raw Lisp between the calls (sequencing, the
; checks on what ACL2 returned, the refusal and fault texts) is here, in
; :program mode, where the extractor can read it.
;
; The HOST PRIMITIVES are the `fn-hx-' stubs below: filesystem syscalls that
; decide nothing (lstat, a bounded directory listing, open read-only with no
; follow, pread into a list, pread into a congruent octet buffer, a shared
; flock, fsync of a directory, statfs, realpath).  They have no ACL2
; definition: an extracted program's runtime implements them
; (tools/extract/runtime.scm, `a-hx-'); the SBCL image does not load this
; file yet (host/native/build.lisp), so these stubs are never run there.
; A HANDLE is a natural the runtime issues; it is also the durable file id
; the extent realizer reads (A-DURABLE-EXTENT's FILE): one table.
;
; Results: (:ok . VALUES), or (CLASS TEXT) with CLASS one of :fault
; (exit :fault), :refused and :open-refusal (exit :refused), :usage.  The
; texts are io.lisp's.  Not here yet (refused by name): a store with a state
; checkpoint (its open comes from lane arena-store-2's pages), a writable
; open, a repair.
(in-package "ACL2")

; ---------------------------------------------------------------------------
; The host primitives (stubs; the runtime implements them).

(defmacro fn-hx-stub (name)
  `(prog2$ (er hard! ',name "~x0 is a host primitive: no ACL2 definition runs" ',name)
           nil))

; (:absent) | (:regular SIZE) | (:directory) | (:symlink) | (:other)
(defun fn-hx-lstat (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-lstat))
; (:ok NAMES MORE) with at most LIMIT names (directory order), or (:error TEXT)
(defun fn-hx-list-dir (path limit)
  (declare (xargs :mode :program) (ignore path limit)) (fn-hx-stub fn-hx-list-dir))
; open(PATH, O_RDONLY|O_NOFOLLOW) and fstat: (:ok HANDLE SIZE REGULARP) or (:error ERRNO TEXT)
(defun fn-hx-open (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-open))
; up to N octets at OFF (fewer only at end of file): (:ok OCTETS) or (:error TEXT)
(defun fn-hx-pread (h off n) (declare (xargs :mode :program) (ignore h off n)) (fn-hx-stub fn-hx-pread))
; the buffer's array := N octets at OFF, its fill := the count read: (mv COUNT BUF)
(defun fn-hx-fill (h off n fn-octets-lg)
  (declare (xargs :mode :program :stobjs fn-octets-lg) (ignore h off n))
  (prog2$ (fn-hx-stub fn-hx-fill) (mv 0 fn-octets-lg)))
; open PATH read-only, no follow, regular, flock(LOCK_SH|LOCK_NB), kept for
; the process: :ok | :locked | (:error ERRNO TEXT) | :not-regular
(defun fn-hx-lock-shared (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-lock-shared))
; :ok | (:error TEXT)
(defun fn-hx-fsync-dir (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-fsync-dir))
; the raw struct statfs (4096 octets) or NIL
(defun fn-hx-statfs (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-statfs))
; realpath(3) as octets, or NIL
(defun fn-hx-realpath (path) (declare (xargs :mode :program) (ignore path)) (fn-hx-stub fn-hx-realpath))
; the host's operating system: :linux | :openbsd | :darwin | :other
(defun fn-hx-os () (declare (xargs :mode :program)) (fn-hx-stub fn-hx-os))
; a line to standard error (a warning the open prints and proceeds past)
(defun fn-hx-warn (text) (declare (xargs :mode :program) (ignore text)) (fn-hx-stub fn-hx-warn))

; ---------------------------------------------------------------------------
; Small helpers (what io.lisp's fnn-* utilities do).

(defun fn-xo-join (dir name)
  (declare (xargs :mode :program))
  (concatenate 'string dir "/" name))

(defun fn-xo-chars (octets)
  (declare (xargs :mode :program))
  (if (consp octets) (cons (code-char (car octets)) (fn-xo-chars (cdr octets))) nil))

(defun fn-xo-string (octets)
  ; octets to an ACL2 string, one character per octet (the runtime's strings
  ; are byte strings; a path or a line ACL2 made is ASCII or UTF-8 octets)
  (declare (xargs :mode :program))
  (coerce (fn-xo-chars octets) 'string))

(defun fn-xo-codes (cs)
  (declare (xargs :mode :program))
  (if (consp cs) (cons (char-code (car cs)) (fn-xo-codes (cdr cs))) nil))

(defun fn-xo-octets (s)
  (declare (xargs :mode :program))
  (fn-xo-codes (coerce s 'list)))

(defun fn-xo-fault (text) (declare (xargs :mode :program)) (list :fault text))
(defun fn-xo-okp (r) (declare (xargs :mode :program)) (and (consp r) (eq (car r) :ok)))

(defun fn-xo-insert-string (s l)
  (declare (xargs :mode :program))
  (if (or (endp l) (string< s (car l))) (cons s l) (cons (car l) (fn-xo-insert-string s (cdr l)))))

(defun fn-xo-sort-strings (l acc)
  (declare (xargs :mode :program))
  (if (endp l) acc (fn-xo-sort-strings (cdr l) (fn-xo-insert-string (car l) acc))))

; fnn-check-regular: (:ok STAT) with STAT (:regular SIZE) or (:absent); a fault otherwise
(defun fn-xo-check-regular (path)
  (declare (xargs :mode :program))
  (let ((st (fn-hx-lstat path)))
    (if (member-eq (car st) '(:regular :absent))
        (list :ok st)
      (fn-xo-fault (concatenate 'string "refusing non-regular path: " path)))))

; fnn-safe-directory (no create)
(defun fn-xo-safe-directory (path)
  (declare (xargs :mode :program))
  (let ((st (fn-hx-lstat path)))
    (cond ((eq (car st) :absent)
           (fn-xo-fault (concatenate 'string "missing store directory: " path)))
          ((not (eq (car st) :directory))
           (fn-xo-fault (concatenate 'string "refusing non-directory store path: " path)))
          (t (list :ok)))))

; fnn-read-regular-bounded over a regular file: (:ok OCTETS), (:overbound) or a fault
(defun fn-xo-read-bounded (path maximum)
  (declare (xargs :mode :program))
  (let ((o (fn-hx-open path)))
    (cond ((not (fn-xo-okp o))
           (fn-xo-fault (concatenate 'string "cannot read store file: " path)))
          ((not (nth 3 o))
           (fn-xo-fault (concatenate 'string "refusing non-regular store file: " path)))
          ((> (nth 2 o) maximum) (list :overbound))
          (t (let ((r (fn-hx-pread (nth 1 o) 0 (nth 2 o))))
               (if (fn-xo-okp r) (list :ok (cadr r))
                 (fn-xo-fault (concatenate 'string "cannot read store file: " path))))))))

; fnn-list-directory-bounded: (:ok NAMES) or a fault past the bound
(defun fn-xo-list-bounded (path limit namespace)
  (declare (xargs :mode :program))
  (let ((r (fn-hx-list-dir path limit)))
    (cond ((not (fn-xo-okp r))
           (fn-xo-fault (concatenate 'string "cannot enumerate " namespace ": " path)))
          ((caddr r) (fn-xo-fault (concatenate 'string namespace " exceeds ACL2 observation bound")))
          (t (list :ok (cadr r))))))

; ---------------------------------------------------------------------------
; The filesystem identity (fnn-check-filesystem-identity, the open's arm).

(defun fn-xo-mountinfo-fold (octets line overlong limit best path)
  ; fnn-mountinfo-best: the lines of /proc/self/mountinfo through ACL2's step
  (declare (xargs :mode :program))
  (cond ((endp octets)
         (if (or overlong line)
             (fn-smid-mountinfo-step best (if overlong :overlong (reverse line)) path)
           best))
        ((equal (car octets) 10)
         (fn-xo-mountinfo-fold (cdr octets) nil nil limit
                               (if (or overlong line)
                                   (fn-smid-mountinfo-step best (if overlong :overlong (reverse line)) path)
                                 best)
                               path))
        (overlong (fn-xo-mountinfo-fold (cdr octets) line t limit best path))
        ((>= (len line) limit) (fn-xo-mountinfo-fold (cdr octets) line t limit best path))
        (t (fn-xo-mountinfo-fold (cdr octets) (cons (car octets) line) nil limit best path))))

(defun fn-xo-read-proc (h off acc)
  ; a /proc file reads to end of file (its size is 0)
  (declare (xargs :mode :program))
  (let ((r (fn-hx-pread h off 65536)))
    (if (or (not (fn-xo-okp r)) (endp (cadr r)))
        acc
      (fn-xo-read-proc h (+ off (len (cadr r))) (append acc (cadr r))))))

(defun fn-xo-filesystem-observation (root)
  (declare (xargs :mode :program))
  (let ((raw (fn-hx-statfs root)))
    (if (null raw)
        (list :unobserved)
      (case (fn-hx-os)
        (:linux
         (let ((path (fn-hx-realpath root))
               (o (fn-hx-open "/proc/self/mountinfo")))
           (if (or (null path) (not (fn-xo-okp o)))
               (list :unobserved)
             (fn-smid-linux-observation
              (take 8 (nthcdr 56 raw))
              (fn-xo-mountinfo-fold (fn-xo-read-proc (nth 1 o) 0 nil) nil nil
                                    (fn-smid-mountinfo-line-max) nil path)))))
        (otherwise (list :unobserved))))))

(defun fn-xo-record-observation (root)
  (declare (xargs :mode :program))
  (let* ((path (fn-xo-join root "filesystem-identity.fnmi"))
         (c (fn-xo-check-regular path)))
    (cond ((not (fn-xo-okp c)) c)
          ((eq (car (cadr c)) :absent) (list :ok (list :absent)))
          (t (let ((r (fn-xo-read-bounded path (fn-smid-record-frame-limit))))
               (cond ((eq (car r) :overbound) (list :ok (list :present nil nil)))
                     ((not (fn-xo-okp r)) r)
                     ((< (len (cadr r)) 32) (list :ok (list :present (cadr r) nil)))
                     (t (let ((trailer (fn-frame-trailer (take (- (len (cadr r)) 32) (cadr r)))))
                          (if (eq trailer :bad)
                              (fn-xo-fault "ACL2 refused to trail a protected prefix")
                            (list :ok (list :present (cadr r) trailer)))))))))))

(defun fn-xo-filesystem-identity (root)
  (declare (xargs :mode :program))
  (let ((rec (fn-xo-record-observation root))
        (cfg (fn-xo-check-regular (fn-xo-join root "config.json"))))
    (cond ((not (fn-xo-okp rec)) rec)
          ((not (fn-xo-okp cfg)) cfg)
          (t (let ((verdict (fn-smid-open-decision (cadr rec) (fn-xo-filesystem-observation root)
                                                   (eq (car (cadr cfg)) :regular))))
               (cond ((and (consp verdict) (eq (car verdict) :open-unrecorded))
                      (prog2$ (fn-hx-warn (fn-xo-string (fn-smid-unrecorded-warning verdict)))
                              (list :ok)))
                     ((equal verdict '(:open)) (list :ok))
                     (t (let ((text (fn-smid-refusal-text verdict)))
                          (if text
                              (list :open-refusal (fn-xo-string text))
                            (fn-xo-fault "ACL2 returned no text for a filesystem refusal"))))))))))

; ---------------------------------------------------------------------------
; Acquire (fnn-acquire, shared lock) and the profile (fnn-load-config).

(defun fn-xo-ascii-p (l)
  (declare (xargs :mode :program))
  (or (endp l) (and (< (car l) 128) (fn-xo-ascii-p (cdr l)))))

(defun fn-xo-checkpoint-name-result (value description)
  (declare (xargs :mode :program))
  (if (and (fn-cbor-octet-listp value) value
           (not (member 47 value)) (not (member 0 value))
           (fn-xo-ascii-p value))
      (list :ok (fn-xo-string value))
    (fn-xo-fault (concatenate 'string "ACL2 returned invalid " description))))

(defun fn-xo-load-config (root)
  (declare (xargs :mode :program))
  (let* ((path (fn-xo-join root "config.json"))
         (c (fn-xo-check-regular path)))
    (if (not (fn-xo-okp c)) c
      (let ((raw (if (eq (car (cadr c)) :absent)
                     (fn-xo-fault (concatenate 'string "invalid durable config: no file " path))
                   (fn-xo-read-bounded path 16384))))
        (cond ((eq (car raw) :overbound)
               (fn-xo-fault (concatenate 'string "store file exceeds bound: " path)))
              ((not (fn-xo-okp raw)) raw)
              ((and (consp (cadr raw)) (equal (car (cadr raw)) 123))
               (list :open-refusal (fn-store-metadata-config-refusal-text '(:refused :store-format))))
              (t (let ((verdict (fn-store-metadata-config-open (cadr raw))))
                   (cond ((and (consp verdict) (eq (car verdict) :opened)
                               (fn-store-profile-admittedp (cadr verdict)))
                          (list :ok (cadr verdict)))
                         ((and (consp verdict) (eq (car verdict) :refused))
                          (let ((text (fn-store-metadata-config-refusal-text verdict)))
                            (if (stringp text) (list :open-refusal text)
                              (fn-xo-fault "ACL2 refused the store profile without naming a reason"))))
                         ((equal verdict '(:rejected))
                          (fn-xo-fault "ACL2 rejected durable configuration frame"))
                         (t (fn-xo-fault "ACL2 returned a malformed profile open verdict"))))))))))

; (:ok CONFIG) or the refusal
(defun fn-xo-acquire (root)
  (declare (xargs :mode :program))
  (let ((r (fn-xo-safe-directory root)))
    (if (not (fn-xo-okp r)) r
      (let ((fence (fn-xo-checkpoint-name-result (fn-store-checkpoint-clone-fence-name)
                                                 "clone fence name")))
        (cond ((not (fn-xo-okp fence)) fence)
              ((not (eq (car (fn-hx-lstat (fn-xo-join root (cadr fence)))) :absent))
               (list :refused "clone is fenced pending durable incarnation rollover"))
              (t
               (let ((r (fn-xo-filesystem-identity root)))
                 (if (not (fn-xo-okp r)) r
                   (let ((r (fn-xo-safe-directory (fn-xo-join root "staging"))))
                     (if (not (fn-xo-okp r)) r
                       (let ((lock (fn-hx-lock-shared (fn-xo-join root "writer.lock"))))
                         (cond ((eq lock :locked) (list :refused "store is already locked"))
                               ((eq lock :not-regular) (fn-xo-fault "refusing non-regular writer lock"))
                               ((and (consp lock) (equal (cadr lock) 40)) ; ELOOP
                                (fn-xo-fault "refusing writer-lock symlink"))
                               ((not (eq lock :ok))
                                (fn-xo-fault (concatenate 'string "cannot open writer lock: "
                                                          (if (consp lock) (caddr lock) ""))))
                               (t (let ((config (fn-xo-load-config root)))
                                    (cond ((not (fn-xo-okp config)) config)
                                          ((not (fn-store-profile-logp (cadr config)))
                                           (fn-xo-fault "a store that is not on the record log opened"))
                                          (t (let ((r (fn-xo-safe-directory (fn-xo-join root "journal"))))
                                               (if (fn-xo-okp r) config r))))))))))))))))))

; ---------------------------------------------------------------------------
; The configuration history (fnn-config-records).

(defun fn-xo-read-config-entries (dir names acc)
  (declare (xargs :mode :program))
  (if (endp names) (list :ok (reverse acc))
    (let* ((path (fn-xo-join dir (car names)))
           (c (fn-xo-check-regular path)))
      (if (not (fn-xo-okp c)) c
        (let ((r (fn-xo-read-bounded path 65538)))
          (cond ((eq (car r) :overbound) (fn-xo-fault (concatenate 'string "store file exceeds bound: " path)))
                ((not (fn-xo-okp r)) r)
                (t (fn-xo-read-config-entries dir (cdr names)
                                              (cons (list (fn-xo-octets (car names)) (cadr r)) acc)))))))))

(defun fn-xo-config-plan-ok (plan observed-names)
  (declare (xargs :mode :program))
  (or (endp plan)
      (let ((e (car plan)))
        (and (true-listp e) (equal (len e) 2) (stringp (car e))
             (fn-cbor-octet-listp (cadr e))
             (not (member (code-char 47) (coerce (car e) 'list)))
             (member-equal (car e) observed-names)
             (fn-xo-config-plan-ok (cdr plan) observed-names)))))

(defun fn-xo-config-records (root config)
  ; (:ok RECORDS): the config octets in ACL2's canonical order
  (declare (xargs :mode :program))
  (let ((limit (fn-store-config-observation-limit config)))
    (if (not (and (integerp limit) (> limit 0)))
        (fn-xo-fault "ACL2 returned a malformed configuration generation bound")
      (let* ((dir (fn-xo-join root "config"))
             (listed (fn-hx-list-dir dir limit)))
        (cond ((not (fn-xo-okp listed)) (fn-xo-fault "cannot enumerate configuration history"))
              ((caddr listed) (fn-xo-fault "configuration namespace exceeds ACL2 observation bound"))
              (t (let* ((names (fn-xo-sort-strings (cadr listed) nil))
                        (entries (fn-xo-read-config-entries dir names nil)))
                   (if (not (fn-xo-okp entries)) entries
                     (let ((value (fn-store-config-observation (cadr entries) limit)))
                       (cond ((not (and (true-listp value) (equal (len value) 3)
                                        (eq (car value) :ok) (null (cadr value))
                                        (true-listp (caddr value))))
                              (fn-xo-fault "ACL2 refused configuration namespace observation"))
                             ((not (fn-xo-config-plan-ok (caddr value) names))
                              (fn-xo-fault "ACL2 returned malformed configuration namespace entry"))
                             ((endp (caddr value))
                              (fn-xo-fault "refusing store with no durable configuration record"))
                             (t (list :ok (strip-cadrs (caddr value))))))))))))))

; ---------------------------------------------------------------------------
; The replay stream (fnn-recover-log-stream-*): REPLAY is
; (ACC CHUNK-REVERSED OCTETS NEXT PLACES-REVERSED FOLD).

(defun fn-xo-some (l)
  (declare (xargs :mode :program))
  (and (consp l) (or (car l) (fn-xo-some (cdr l)))))

(defun fn-xo-replay-flush (replay fn-arena)
  ; (mv RESULT REPLAY fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (if (null (nth 1 replay))
      (mv (list :ok) replay fn-arena)
    (let* ((chunk (reverse (nth 1 replay)))
           (places (reverse (nth 4 replay))))
     (mv-let (decoded fold)
      (fn-lgb-decode-next chunk (nth 5 replay))
     (let ((next (if (consp decoded)
                     (fn-store-log-next-txid-of-events decoded (nth 3 replay))
                   (nth 3 replay))))
      (mv-let (acc fn-arena)
        (if (fn-xo-some places)
            (fn-arx-intern-step (nth 0 replay) decoded chunk places fn-arena)
          (fn-srs-intern-step (nth 0 replay) decoded fn-arena))
        (if (eq acc :bad)
            (mv (fn-xo-fault "ACL2 replay rejected committed transaction history") replay fn-arena)
          (mv (list :ok) (list acc nil 0 next nil fold) fn-arena))))))))

(defun fn-xo-replay-take (replay record place fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (r replay fn-arena)
    (if (and (nth 1 replay) (fn-srs-chunk-fullp (nth 2 replay)))
        (fn-xo-replay-flush replay fn-arena)
      (mv (list :ok) replay fn-arena))
    (if (not (fn-xo-okp r))
        (mv r replay fn-arena)
      (mv (list :ok)
          (list (nth 0 replay) (cons record (nth 1 replay)) (+ (nth 2 replay) (len record))
                (nth 3 replay) (cons place (nth 4 replay)) (nth 5 replay))
          fn-arena))))

(defun fn-xo-replay-take-all (replay records file places fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (if (endp records)
      (mv (list :ok) replay fn-arena)
    (mv-let (r replay fn-arena)
      (fn-xo-replay-take replay (car records)
                         (and file (consp places) (cons file (car places)))
                         fn-arena)
      (if (not (fn-xo-okp r))
          (mv r replay fn-arena)
        (fn-xo-replay-take-all replay (cdr records) file
                               (if (consp places) (cdr places) places) fn-arena)))))

; ---------------------------------------------------------------------------
; One segment's stream (fnn-log-stream-segment, read-only, the full replay's
; finish) and ACL2's probe of the rest (fnn-log-probe-tail).

(defun fn-xo-pread-exact (h off n)
  (declare (xargs :mode :program))
  (let ((r (fn-hx-pread h off n)))
    (if (and (fn-xo-okp r) (equal (len (cadr r)) n))
        r
      (fn-xo-fault "log segment shorter than its extent"))))

(defun fn-xo-probe-tail (h extent unit max ps)
  (declare (xargs :mode :program))
  (if (fn-lgdm-done-p ps extent)
      (list :ok ps)
    (let* ((q (fn-lgdm-q ps))
           (hd (fn-xo-pread-exact h q (fn-lgdm-header-len ps extent))))
      (if (not (fn-xo-okp hd)) hd
        (let* ((n (fn-lgdm-entry-len (cadr hd) ps extent))
               (e (if n (fn-xo-pread-exact h q n) (list :ok nil))))
          (if (not (fn-xo-okp e)) e
            (fn-xo-probe-tail h extent unit max
                              (fn-lgdm-step (cadr hd) (and n (cadr e)) ps unit max))))))))

(defun fn-xo-walk (h extent unit max st file replay fn-octets-lg fn-arena)
  ; (mv RESULT ST REPLAY fn-octets-lg fn-arena): the entries to the stop
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena)))
  (if (fn-lgw-stop st)
      (mv (list :ok) st replay fn-octets-lg fn-arena)
    (let* ((pos (fn-lgw-pos st))
           (hd (fn-xo-pread-exact h pos (fn-lgw-header-len st extent))))
      (if (not (fn-xo-okp hd))
          (mv hd st replay fn-octets-lg fn-arena)
        (let ((n (fn-lgw-entry-len (cadr hd) st extent)))
          (mv-let (count fn-octets-lg)
            (fn-hx-fill h pos (if n n 0) fn-octets-lg)
            (if (not (equal count (if n n 0)))
                (mv (fn-xo-fault "log segment shorter than its extent") st replay fn-octets-lg fn-arena)
              (mv-let (took records next)
                (fn-lgw-step-buf-nf st unit max extent fn-octets-lg)
                (if (not took)
                    (fn-xo-walk h extent unit max next file replay fn-octets-lg fn-arena)
                  (let ((places (fn-lgb-entry-places pos (len records) unit fn-octets-lg)))
                    (mv-let (r replay fn-arena)
                      (fn-xo-replay-take-all replay records file places fn-arena)
                      (if (not (fn-xo-okp r))
                          (mv r st replay fn-octets-lg fn-arena)
                        (fn-xo-walk h extent unit max next file replay
                                    fn-octets-lg fn-arena)))))))))))))

; (mv RESULT REPLAY fn-octets-lg fn-arena), RESULT (:ok KERNEL)
(defun fn-xo-stream-segment (h extent unit max genesis label replay fn-octets-lg fn-arena)
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena)))
  (mv-let (r st replay fn-octets-lg fn-arena)
    (fn-xo-walk h extent unit max (fn-lgw-start genesis 1) h replay fn-octets-lg fn-arena)
    (mv-let (count fn-octets-lg) (fn-hx-fill h 0 0 fn-octets-lg)
      (declare (ignore count))
      (if (not (fn-xo-okp r))
          (mv r replay fn-octets-lg fn-arena)
        ; the replay's fold of this segment's txids, taken from its decode
        (mv-let (r replay fn-arena) (fn-xo-replay-flush replay fn-arena)
          (if (not (fn-xo-okp r))
              (mv r replay fn-octets-lg fn-arena)
            (let* ((st (fn-lgw-set-next st (nth 5 replay)))
                   (replay (update-nth 5 1 replay))
                   (probe (fn-xo-probe-tail h extent unit max (fn-lgdm-start st))))
              (if (not (fn-xo-okp probe))
                  (mv probe replay fn-octets-lg fn-arena)
                (let ((verdict (fn-lgdm-effective (fn-lgdm-verdict st (cadr probe) extent)
                                                  label nil nil)))
                  (if (fn-lgdm-refused-p verdict)
                      (let ((text (fn-lgdm-refusal-text verdict label)))
                        (mv (if text (list :open-refusal text)
                              (fn-xo-fault "ACL2 refused a log segment without a line"))
                            replay fn-octets-lg fn-arena))
                    (mv (list :ok (fn-lgw-kernel st)) replay fn-octets-lg fn-arena)))))))))))

; A segment opened for reading (fnn-log-observed-extent, fnn-log-open-segment
; read-only): (:ok HANDLE EXTENT) or the refusal.
(defun fn-xo-open-segment (path unit)
  (declare (xargs :mode :program))
  (let ((st (fn-hx-lstat path)))
    (cond ((eq (car st) :absent) (list :refused (concatenate 'string "no log segment at " path)))
          ((not (eq (car st) :regular))
           (fn-xo-fault (concatenate 'string "refusing non-regular path: " path)))
          ((not (fn-lg-extent-okp (cadr st) unit))
           (list :usage "log extent is not a positive number of units"))
          (t (let ((o (fn-hx-open path)))
               (cond ((not (fn-xo-okp o))
                      (fn-xo-fault (concatenate 'string "cannot open log segment: " path)))
                     ((not (equal (nth 2 o) (cadr st)))
                      (list :refused (concatenate 'string "log segment " path " is not its extent long")))
                     (t (list :ok (nth 1 o) (cadr st)))))))))

(defun fn-xo-segment-path (root k)
  (declare (xargs :mode :program))
  (let ((name (fn-lgs-segment-name k)))
    (if (and (stringp name) (< 0 (length name))
             (not (member (code-char 47) (coerce name 'list)))
             (eql (fn-lgs-segment-index name) k))
        (list :ok (fn-xo-join (fn-xo-join root "journal") name) name)
      (fn-xo-fault "ACL2 returned an invalid log segment name"))))

; fnn-log-scan-segments with the full replay's places: (mv RESULT REPLAY
; fn-octets-lg fn-arena), RESULT (:ok KERNEL) of the active (last) segment.
(defun fn-xo-scan (root scan genesis unit max replay fn-octets-lg fn-arena)
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena)))
  (if (endp scan)
      (mv (fn-xo-fault "the log's open plan named no segment") replay fn-octets-lg fn-arena)
    (let ((p (fn-xo-segment-path root (car scan))))
      (if (not (fn-xo-okp p))
          (mv p replay fn-octets-lg fn-arena)
        (let ((active (endp (cdr scan))))
          (if (and active
                   (let ((st (fn-hx-lstat (cadr p))))
                     (and (eq (car st) :regular) (not (fn-lg-extent-okp (cadr st) unit)))))
              (mv (list :refused (concatenate 'string "log segment " (cadr p)
                                              " is an interrupted rotation: open it writable (recover)"))
                  replay fn-octets-lg fn-arena)
            (let ((seg (fn-xo-open-segment (cadr p) unit)))
              (if (not (fn-xo-okp seg))
                  (mv seg replay fn-octets-lg fn-arena)
                (mv-let (r replay fn-octets-lg fn-arena)
                  (fn-xo-stream-segment (nth 1 seg) (nth 2 seg) unit max genesis (caddr p)
                                        replay fn-octets-lg fn-arena)
                  (cond ((not (fn-xo-okp r)) (mv r replay fn-octets-lg fn-arena))
                        (active (mv r replay fn-octets-lg fn-arena))
                        (t (fn-xo-scan root (cdr scan) (fn-lgc-last (cadr r)) unit max
                                       replay fn-octets-lg fn-arena))))))))))))

; ---------------------------------------------------------------------------
; The open (fnn-reader-prepare with a store, read-only; fnn-recover-log's
; full-replay arm; the recovery barriers).  (mv RESULT fn-octets-lg fn-arena
; state), RESULT (:ok FRONTIER RECORD-COUNT-UNKNOWN) or the refusal.

(defun fn-xo-barriers (dirs phase state)
  ; each directory fenced, then ACL2 observes the barrier (fnn-observe ->
  ; fn-store-sn-io); its phase must stay :recovering or reach :ready
  (declare (xargs :mode :program :stobjs state))
  (if (endp dirs)
      (mv (if (eq phase :ready) (list :ok)
            (fn-xo-fault "ACL2 did not complete all recovery barriers"))
          state)
    (let ((f (fn-hx-fsync-dir (car dirs))))
      (if (not (eq f :ok))
          (mv-let (erp val state) (fn-store-sn-io :recovery-barrier :uncertain state)
            (declare (ignore erp val))
            (mv (list :indeterminate "cannot establish recovered log frontier") state))
        (mv-let (erp phase state) (fn-store-sn-io :recovery-barrier :ok state)
          (cond (erp (mv (list :indeterminate "ACL2 could not record recovery-barrier observation") state))
                ((not (member-eq phase '(:recovering :ready)))
                 (mv (fn-xo-fault "ACL2 rejected recovered barrier ordering") state))
                (t (fn-xo-barriers (cdr dirs) phase state))))))))

(defun fn-xo-parent (path)
  (declare (xargs :mode :program))
  (let* ((cs (coerce path 'list))
         (r (member (code-char 47) (reverse cs))))
    (if (or (endp r) (endp (cdr r))) "/" (coerce (reverse (cdr r)) 'string))))

(defun fn-xo-open-store (root fn-octets-lg fn-arena state)
  (declare (xargs :mode :program :stobjs (fn-octets-lg fn-arena state)))
  (let ((config (fn-xo-acquire root)))
    (if (not (fn-xo-okp config))
        (mv config fn-octets-lg fn-arena state)
      (let ((config (cadr config)))
        (mv-let (erp action state) (fn-store-sn-reset state)
          (declare (ignore action))
          (if erp
              (mv (fn-xo-fault "ACL2 error in fn-store-sn-reset") fn-octets-lg fn-arena state)
            (let* ((cname (fn-store-sco-file-name))
                   (cpath (fn-xo-join root cname))
                   (cst (fn-hx-lstat cpath)))
              (if (not (eq (car cst) :absent))
                  (mv (list :fault "extract: a store with a state checkpoint is not opened by this program yet (its open comes from the page store)")
                      fn-octets-lg fn-arena state)
                (mv-let (erp val state) (fn-store-sco-clear state)
                  (declare (ignore erp val))
                  (let ((names (fn-xo-list-bounded (fn-xo-join root "journal") (fn-lgs-listing-bound)
                                                   "log segment")))
                    (if (not (fn-xo-okp names))
                        (mv names fn-octets-lg fn-arena state)
                      (let ((plan (fn-lgs-open-plan (cadr names) nil)))
                        (cond
                         ((not (and (consp plan) (member-eq (car plan) '(:scan :refused))))
                          (mv (fn-xo-fault "ACL2 returned a malformed log open plan")
                              fn-octets-lg fn-arena state))
                         ((equal plan '(:refused :no-segment))
                          (mv (fn-xo-fault (concatenate 'string "missing store directory: " root
                                                        "/journal has no log segment (an init that did not finish: run init again)"))
                              fn-octets-lg fn-arena state))
                         ((eq (car plan) :refused)
                          (mv (list :open-refusal
                                    (concatenate 'string "open refused reason="
                                                 (string-downcase (symbol-name (cadr plan)))
                                                 ": the log's segments do not hold the history"))
                              fn-octets-lg fn-arena state))
                         (t
                          (let ((choice (fn-store-sco-select :absent 0 0 config)))
                            (if (not (and (consp choice) (eq (car choice) :full-replay)))
                                (mv (fn-xo-fault "ACL2 returned a malformed checkpoint selection")
                                    fn-octets-lg fn-arena state)
                              (let ((config-records (fn-xo-config-records root config)))
                                (if (not (fn-xo-okp config-records))
                                    (mv config-records fn-octets-lg fn-arena state)
                                  (let ((fn-arena (fn-arena-clear fn-arena)))
                                    (mv-let (r replay fn-octets-lg fn-arena)
                                      (fn-xo-scan root (cadr plan) *fn-lg-genesis*
                                                  (fn-store-log-unit)
                                                  (fn-store-profile-max-record-octets config)
                                                  (list nil nil 0 0 nil 1)
                                                  fn-octets-lg fn-arena)
                                      (if (not (fn-xo-okp r))
                                          (mv r fn-octets-lg fn-arena state)
                                        (mv-let (f replay fn-arena) (fn-xo-replay-flush replay fn-arena)
                                          (if (not (fn-xo-okp f))
                                              (mv f fn-octets-lg fn-arena state)
                                            (let* ((kernel (cadr r))
                                                   (next (fn-store-log-next-txid-join
                                                          (fn-store-log-next-txid-join (nth 3 replay) 0)
                                                          (fn-lgc-next-txid kernel))))
                                              (mv-let (erp action state)
                                                (fn-store-sn-recover-rows (fn-srs-rows (nth 0 replay))
                                                                          next (cadr config-records) state)
                                                (declare (ignore erp))
                                                (cond
                                                 ((eq action :refused)
                                                  (mv-let (erp text state) (fn-store-open-refusal-text state)
                                                    (declare (ignore erp))
                                                    (mv (if (stringp text) (list :open-refusal text)
                                                          (fn-xo-fault "ACL2 refused the open without naming a reason"))
                                                        fn-octets-lg fn-arena state)))
                                                 ((not (eq action :recovering))
                                                  (mv-let (erp stop state) (fn-store-open-stop-text state)
                                                    (declare (ignore erp))
                                                    (mv (fn-xo-fault
                                                         (if (stringp stop)
                                                             (concatenate 'string "ACL2 replay rejected committed transaction history or configuration history: " stop)
                                                           "ACL2 replay rejected committed transaction history or configuration history"))
                                                        fn-octets-lg fn-arena state)))
                                                 (t
                                                  (mv-let (b state)
                                                    (fn-xo-barriers (list (fn-xo-join root "journal") root
                                                                          (fn-xo-parent root))
                                                                    nil state)
                                                    (mv (if (fn-xo-okp b) (list :ok next) b)
                                                        fn-octets-lg fn-arena state)))))))))))))))))))))))))))))
