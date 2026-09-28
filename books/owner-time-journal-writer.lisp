; fn: the decision journal's writer never keeps a torn line (lane
; health-truth-journal, 2026-09-28; PKT-872; PRF-360).
;
; books/owner-time-journal.lisp proves that the journal a run writes reads
; back whole and replays to agreement.  That assumed every line the writer
; thread took reached the file whole.  Lane fitness's full-disk run (f2-full,
; planning/evidence/fitness-2026-09-28.md) showed the other case: an append
; hit ENOSPC part-way through a line (`18416 2 24487'), the writer counted
; the line dropped, and the next line that fit was appended AFTER the torn
; octets, so the file kept a line that is neither an entry nor a tail, and
; `store journal' read `malformed-at-18416' for that store forever.
;
; The writer's rule, every decision ACL2's (the host calls each function
; marked THE HOST'S CALL; host/native/io.lisp fnn-journal-write,
; host/native/owner.lisp fnn-owner-journal-open):
;
;   - The writer carries (OFFSET OWE CLOSED): OFFSET the length of the file's
;     whole lines, OWE that an entry was lost since the last whole one (a
;     failed write, or the sink dropped it at its bound), CLOSED that a
;     failed write could not be undone.
;   - A failed write is undone: the host truncates the file back to OFFSET
;     (ftruncate, which needs no free space).  When the truncation itself
;     fails the writer CLOSES the journal for the run: nothing more is
;     appended after the torn octets, which stay the file's tail.
;   - The next entry written after a loss carries the MARK line first
;     (`*fn-otm-mark-entry*', OP 7): replay reads it as (:gap N), N the first
;     sequence number missing.  A gap is named where it happened, never
;     inferred from a later number that may coincide.
;   - At open the file is cut to its last whole line (a process that died
;     mid-append leaves a torn tail), read backwards in chunks of
;     `*fn-otm-jw-open-chunk*' octets: bounded work per step.
;
; KEYSTONE fn-otm-jw-file-reads-agrees-or-gap: for any entries the writer is
; offered, any fate of each (written, dropped by the sink, a write that
; failed after any number of its octets landed, its truncation holding or
; not) and so at every process-death cut (a death mid-append is a failed
; write that is never truncated), the file reads back :whole or :torn --
; never :malformed -- and replays to exactly the verdict of the entries that
; landed before the first loss, or, when that prefix agrees and an entry was
; written after the loss, (:gap N) with N one past the last entry replayed;
; fn-otm-jw-gap-names-the-first-missing: when the offered entries replay to
; agreement, N is the sequence number of the first entry lost.
; fn-otm-jw-open-cut-of-a-written-file: the open's cut of such a file is its
; whole lines.
(in-package "ACL2")
(include-book "owner-time-journal")
(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; The writer's state (OFFSET OWE CLOSED)

(defun fn-otm-jw-make (offset owe closed)
  (declare (xargs :guard t))
  (list (nfix offset) (if owe t nil) (if closed t nil)))

(defun fn-otm-jw-offset (w)
  (declare (xargs :guard t))
  (if (consp w) (nfix (car w)) 0))

(defun fn-otm-jw-owe (w)
  (declare (xargs :guard t))
  (if (and (consp w) (consp (cdr w)) (cadr w)) t nil))

(defun fn-otm-jw-closed (w)
  (declare (xargs :guard t))
  (if (and (consp w) (consp (cdr w)) (consp (cddr w)) (caddr w)) t nil))

; THE HOST'S CALL at open (host/native/owner.lisp fnn-owner-journal-open),
; after the open's cut: OFFSET the file's length.
(defun fn-otm-jw-init (offset)
  (declare (xargs :guard t))
  (fn-otm-jw-make offset nil nil))

; THE HOST'S CALL when the queue says the sink dropped a journal entry
; before this one (host/native/io.lisp fnn-log-writer-loop, a :journal-gap
; item).
(defun fn-otm-jw-drop (w)
  (declare (xargs :guard t))
  (fn-otm-jw-make (fn-otm-jw-offset w) t (fn-otm-jw-closed w)))

(defun fn-otm-mark-line ()
  (declare (xargs :guard t))
  (fn-otm-jline *fn-otm-mark-entry*))

; THE HOST'S CALL for each entry the writer takes: the octets to append (the
; mark first when an entry was lost), or nil when the journal is closed
; (the entry is lost; the sink counts it).
(defun fn-otm-jw-plan (w line)
  (declare (xargs :guard t))
  (cond ((fn-otm-jw-closed w) nil)
        ((fn-otm-jw-owe w) (append (fn-otm-mark-line) line))
        (t line)))

; THE HOST'S CALL after the append of N planned octets: (W' ACTION).
; :written moves OFFSET past them; anything else keeps OFFSET, owes a mark
; and asks the host to truncate the file back to OFFSET.
(defun fn-otm-jw-after (w n outcome)
  (declare (xargs :guard t))
  (if (eq outcome :written)
      (list (fn-otm-jw-make (+ (fn-otm-jw-offset w) (nfix n)) nil nil) :none)
    (list (fn-otm-jw-make (fn-otm-jw-offset w) t nil)
          (list :truncate (fn-otm-jw-offset w)))))

; THE HOST'S CALL after that truncation: OK whether it held.  One that did
; not closes the journal for the run.
(defun fn-otm-jw-truncated (w ok)
  (declare (xargs :guard t))
  (fn-otm-jw-make (fn-otm-jw-offset w) t (not ok)))

; The service log's lines for the writer's two events (THE HOST'S CALLS,
; host/native/owner.lisp fnn-owner-journal-open, host/native/io.lisp
; fnn-journal-write).
(defun fn-otm-jw-cut-line (size cut)
  (declare (xargs :guard t))
  (append (fn-osch-text "decision journal: the previous run's torn last entry (")
          (fn-osch-decimal (nfix (- (nfix size) (nfix cut))))
          (fn-osch-text " octets) was cut; the journal resumes after its last whole entry at octet ")
          (fn-osch-decimal cut)))

(defun fn-otm-jw-closed-line (offset)
  (declare (xargs :guard t))
  (append (fn-osch-text "decision journal: a failed append could not be truncated back to octet ")
          (fn-osch-decimal offset)
          (fn-osch-text "; the journal is closed for this run (its later entries are dropped and counted; the torn tail is cut at the next start)")))

; -----------------------------------------------------------------------------
; The open's cut: the file's whole lines end at its last LF.

(defconst *fn-otm-jw-open-chunk* 4096)

(defun fn-otm-jw-lf-pos (xs)
  ; the position just after the last LF of XS, or nil when it holds none
  (declare (xargs :guard t))
  (if (consp xs)
      (let ((p (fn-otm-jw-lf-pos (cdr xs))))
        (if p (+ 1 p) (if (eql (car xs) 10) 1 nil)))
    nil))

; The whole-file statement: the length of the file's whole lines.
(defun fn-otm-jw-open-cut (file)
  (declare (xargs :guard t))
  (or (fn-otm-jw-lf-pos file) 0))

; THE HOST'S CALL: where the first chunk starts, for a file of SIZE octets.
(defun fn-otm-jw-open-first (size)
  (declare (xargs :guard t))
  (nfix (- (nfix size) *fn-otm-jw-open-chunk*)))

; THE HOST'S CALL for each chunk, read backwards: CHUNK the file's octets
; from START up to where the last chunk began (the file's end the first
; time).  (:cut OFFSET), or (:more START') -- the chunk before, whose end is
; START.
(defun fn-otm-jw-open-step (chunk start)
  (declare (xargs :guard (natp start)))
  (let ((p (fn-otm-jw-lf-pos chunk)))
    (cond (p (list :cut (+ (nfix start) p)))
          ((zp start) (list :cut 0))
          (t (list :more (nfix (- start *fn-otm-jw-open-chunk*)))))))

; -----------------------------------------------------------------------------
; The model of the writer over a run's entries.  ES the entries offered in
; order; FATES one per entry: :drop (the sink dropped it: the host calls
; fn-otm-jw-drop and never writes it), or (OK K TOK): the append succeeded
; (OK), or failed with its first K octets on the file and the truncation
; holding (TOK) or not.  A process that dies mid-append is (nil K nil) as
; its last fate: the file is exactly what that fate leaves.

(defun fn-otm-jw-fate-ok (f) (declare (xargs :guard t)) (and (consp f) (car f) t))
(defun fn-otm-jw-fate-k (f) (declare (xargs :guard t)) (if (consp f) (nfix (if (consp (cdr f)) (cadr f) 0)) 0))
(defun fn-otm-jw-fate-tok (f)
  (declare (xargs :guard t))
  (and (consp f) (consp (cdr f)) (consp (cddr f)) (caddr f) t))

(defun fn-otm-jw-sim (w file es fates)
  ; (mv W' FILE')
  (declare (xargs :guard (true-listp file) :measure (len es) :verify-guards nil))
  (if (consp es)
      (let ((f (if (consp fates) (car fates) :drop)))
        (if (or (eq f :drop) (fn-otm-jw-closed w))
            (fn-otm-jw-sim (fn-otm-jw-drop w) file (cdr es) (cdr fates))
          (let* ((octs (fn-otm-jw-plan w (fn-otm-jline (car es)))))
            (if (fn-otm-jw-fate-ok f)
                (fn-otm-jw-sim (car (fn-otm-jw-after w (len octs) :written))
                               (append file octs) (cdr es) (cdr fates))
              (let* ((r (fn-otm-jw-after w (len octs) :failed))
                     (landed (append file (take (min (fn-otm-jw-fate-k f) (len octs)) octs))))
                (if (fn-otm-jw-fate-tok f)
                    (fn-otm-jw-sim (fn-otm-jw-truncated (car r) t)
                                   (take (cadr (cadr r)) landed) (cdr es) (cdr fates))
                  (fn-otm-jw-sim (fn-otm-jw-truncated (car r) nil)
                                 landed (cdr es) (cdr fates))))))))
    (mv w file)))

; The writer's state as an algebra: the proofs below never open it.
(defthm fn-otm-jw-accessors-of-make
  (and (equal (fn-otm-jw-offset (fn-otm-jw-make o a c)) (nfix o))
       (equal (fn-otm-jw-owe (fn-otm-jw-make o a c)) (if a t nil))
       (equal (fn-otm-jw-closed (fn-otm-jw-make o a c)) (if c t nil))))

(defthm fn-otm-jw-after-facts
  (and (equal (car (fn-otm-jw-after w n :written))
              (fn-otm-jw-make (+ (fn-otm-jw-offset w) (nfix n)) nil nil))
       (implies (not (equal outcome :written))
                (and (equal (car (fn-otm-jw-after w n outcome))
                            (fn-otm-jw-make (fn-otm-jw-offset w) t nil))
                     (equal (cadr (cadr (fn-otm-jw-after w n outcome)))
                            (fn-otm-jw-offset w))))))

(in-theory (disable fn-otm-jw-make fn-otm-jw-offset fn-otm-jw-owe fn-otm-jw-closed
                    fn-otm-jw-after))

; -----------------------------------------------------------------------------
; A fragment: what a proper prefix of a line can be -- digits, and single
; spaces each after a digit; no LF.  The reader takes it as a torn tail.

(defun fn-otm-jw-fragp (xs accp)
  (declare (xargs :guard t))
  (if (consp xs)
      (cond ((and (natp (car xs)) (<= 48 (car xs)) (<= (car xs) 57))
             (fn-otm-jw-fragp (cdr xs) t))
            ((and (equal (car xs) 32) accp) (fn-otm-jw-fragp (cdr xs) nil))
            (t nil))
    t))

(defthm fn-otm-jw-jparse-of-frag
  (implies (fn-otm-jw-fragp xs (if acc t nil))
           (and (equal (mv-nth 1 (fn-otm-jparse xs acc fields entries))
                       (fn-otm-revonto entries nil))
                (not (equal (mv-nth 0 (fn-otm-jparse xs acc fields entries)) :malformed))))
  :hints (("Goal" :induct (fn-otm-jparse xs acc fields entries))))

(local
 (defun fn-otm-jw-digitsp (xs)
   (if (consp xs)
       (and (natp (car xs)) (<= 48 (car xs)) (<= (car xs) 57) (fn-otm-jw-digitsp (cdr xs)))
     t)))

(local
 (defthm fn-otm-jw-digitsp-append
   (equal (fn-otm-jw-digitsp (append a b))
          (and (fn-otm-jw-digitsp a) (fn-otm-jw-digitsp b)))))

(local
 (defthm fn-otm-jw-mod-10-digit
   (implies (posp n) (and (<= 0 (mod n 10)) (< (mod n 10) 10) (integerp (mod n 10))))))

(local
 (defthm fn-otm-jw-dec-octets-digits
   (fn-otm-jw-digitsp (fn-otm-dec-octets n))))

(local
 (defthm fn-otm-jw-dec-octets-consp
   (implies (posp n) (consp (fn-otm-dec-octets n)))))

(local
 (defthm fn-otm-jw-nat-octets-facts
   (and (fn-otm-jw-digitsp (fn-otm-nat-octets n))
        (consp (fn-otm-nat-octets n)))
   :hints (("Goal" :in-theory (enable fn-otm-nat-octets)))))

(local (in-theory (disable fn-otm-nat-octets)))

(local
 (defthm fn-otm-jw-take-of-append
   (implies (true-listp a)
            (equal (take k (append a b))
                   (if (<= (nfix k) (len a))
                       (take k a)
                     (append a (take (- (nfix k) (len a)) b)))))
   :hints (("Goal" :induct (take k a) :in-theory (enable take)))))

(local
 (defthm fn-otm-jw-digitsp-take
   (implies (and (fn-otm-jw-digitsp xs) (<= (nfix k) (len xs)))
            (fn-otm-jw-digitsp (take k xs)))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-otm-jw-fragp-of-digits
   (implies (fn-otm-jw-digitsp xs) (fn-otm-jw-fragp xs accp))))

(local
 (defun fn-otm-jw-digits-ind (xs accp)
   (if (consp xs) (fn-otm-jw-digits-ind (cdr xs) t) accp)))

(local
 (defthm fn-otm-jw-fragp-of-digits-then
   (implies (and (fn-otm-jw-digitsp xs) (consp xs))
            (equal (fn-otm-jw-fragp (append xs rest) accp)
                   (fn-otm-jw-fragp rest t)))
   :hints (("Goal" :induct (fn-otm-jw-digits-ind xs accp)))))

(local
 (defthm fn-otm-jw-true-listp-nat-octets
   (true-listp (fn-otm-nat-octets n))
   :hints (("Goal" :in-theory (enable fn-otm-nat-octets)))))

(local
 (defthm fn-otm-jw-true-listp-jline
   (true-listp (fn-otm-jline ns))))

(local
 (defthm fn-otm-jw-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-otm-jw-take-of-cons
   (implies (posp n)
            (equal (take n (cons a b)) (cons a (take (- n 1) b))))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defun fn-otm-jw-line-ind (ns k)
   (if (consp ns)
       (fn-otm-jw-line-ind (cdr ns) (- (nfix k) (+ 1 (len (fn-otm-nat-octets (car ns))))))
     k)))

(local
 (defthm fn-otm-jw-len-jline
   (equal (len (fn-otm-jline ns))
          (if (consp ns)
              (+ 1 (len (fn-otm-nat-octets (car ns))) (len (fn-otm-jline (cdr ns))))
            0))))

(local (in-theory (disable fn-otm-jw-len-jline)))

(defthm fn-otm-jw-fragp-of-take-jline
  (implies (< (nfix k) (len (fn-otm-jline ns)))
           (fn-otm-jw-fragp (take k (fn-otm-jline ns)) nil))
  :hints (("Goal" :induct (fn-otm-jw-line-ind ns k))))

; -----------------------------------------------------------------------------
; A prefix of whole lines: K octets of the lines of XS are the first
; (fn-otm-jw-cnt K XS) lines whole and then a fragment of the next.

(defun fn-otm-jw-cnt (k xs)
  (declare (xargs :guard t :measure (len xs)))
  (if (and (consp xs) (<= (len (fn-otm-jline (car xs))) (nfix k)))
      (+ 1 (fn-otm-jw-cnt (- (nfix k) (len (fn-otm-jline (car xs)))) (cdr xs)))
    0))

(defun fn-otm-jw-rest (k xs)
  (declare (xargs :guard t :measure (len xs)))
  (if (consp xs)
      (if (<= (len (fn-otm-jline (car xs))) (nfix k))
          (fn-otm-jw-rest (- (nfix k) (len (fn-otm-jline (car xs)))) (cdr xs))
        (take (nfix k) (fn-otm-jline (car xs))))
    nil))

(local
 (defthm fn-otm-jw-true-listp-jlines
   (true-listp (fn-otm-jlines xs))))

(local
 (defthm fn-otm-jw-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-otm-jw-len-zero
   (implies (and (true-listp x) (equal (len x) 0)) (equal x nil))
   :rule-classes nil))

(local
 (defthm fn-otm-jw-jline-empty
   (implies (equal (len (fn-otm-jline ns)) 0)
            (equal (fn-otm-jline ns) nil))
   :hints (("Goal" :use ((:instance fn-otm-jw-len-zero (x (fn-otm-jline ns))))
            :in-theory (disable fn-otm-jline)))))

(local
 (defthm fn-otm-jw-take-len
   (implies (true-listp x) (equal (take (len x) x) x))
   :hints (("Goal" :in-theory (enable take)))))

(defthm fn-otm-jw-take-jlines
  (implies (<= (nfix k) (len (fn-otm-jlines xs)))
           (equal (take k (fn-otm-jlines xs))
                  (append (fn-otm-jlines (take (fn-otm-jw-cnt k xs) xs))
                          (fn-otm-jw-rest k xs))))
  :hints (("Goal" :induct (fn-otm-jw-cnt k xs))))

(defthm fn-otm-jw-fragp-of-rest
  (fn-otm-jw-fragp (fn-otm-jw-rest k xs) nil))

(defthm fn-otm-jw-cnt-bound
  (<= (fn-otm-jw-cnt k xs) (len xs))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; What the writer leaves: the file it started from, then whole lines, then
; at most one fragment.

(defun fn-otm-jw-ents (w e)
  (declare (xargs :guard t))
  (if (fn-otm-jw-owe w) (list *fn-otm-mark-entry* e) (list e)))

(defthm fn-otm-jw-plan-is-jlines
  (implies (not (fn-otm-jw-closed w))
           (equal (fn-otm-jw-plan w (fn-otm-jline e))
                  (fn-otm-jlines (fn-otm-jw-ents w e)))))

(defun fn-otm-jw-whole (w es fates)
  ; the entries whose lines the writer appends whole
  (declare (xargs :guard t :measure (len es) :verify-guards nil))
  (if (consp es)
      (let ((f (if (consp fates) (car fates) :drop)))
        (if (or (eq f :drop) (fn-otm-jw-closed w))
            (fn-otm-jw-whole (fn-otm-jw-drop w) (cdr es) (cdr fates))
          (let* ((ents (fn-otm-jw-ents w (car es)))
                 (n (len (fn-otm-jlines ents))))
            (cond ((fn-otm-jw-fate-ok f)
                   (append ents (fn-otm-jw-whole (car (fn-otm-jw-after w n :written))
                                                 (cdr es) (cdr fates))))
                  ((fn-otm-jw-fate-tok f)
                   (fn-otm-jw-whole (fn-otm-jw-truncated (car (fn-otm-jw-after w n :failed)) t)
                                    (cdr es) (cdr fates)))
                  (t (take (fn-otm-jw-cnt (min (fn-otm-jw-fate-k f) n) ents) ents))))))
    nil))

(defun fn-otm-jw-frag (w es fates)
  ; the fragment a failed append left and no truncation removed
  (declare (xargs :guard t :measure (len es) :verify-guards nil))
  (if (consp es)
      (let ((f (if (consp fates) (car fates) :drop)))
        (if (or (eq f :drop) (fn-otm-jw-closed w))
            (fn-otm-jw-frag (fn-otm-jw-drop w) (cdr es) (cdr fates))
          (let* ((ents (fn-otm-jw-ents w (car es)))
                 (n (len (fn-otm-jlines ents))))
            (cond ((fn-otm-jw-fate-ok f)
                   (fn-otm-jw-frag (car (fn-otm-jw-after w n :written)) (cdr es) (cdr fates)))
                  ((fn-otm-jw-fate-tok f)
                   (fn-otm-jw-frag (fn-otm-jw-truncated (car (fn-otm-jw-after w n :failed)) t)
                                   (cdr es) (cdr fates)))
                  (t (fn-otm-jw-rest (min (fn-otm-jw-fate-k f) n) ents))))))
    nil))

(defthm fn-otm-jw-closed-writes-nothing
  (implies (fn-otm-jw-closed w)
           (and (equal (mv-nth 1 (fn-otm-jw-sim w file es fates)) file)
                (equal (fn-otm-jw-whole w es fates) nil)
                (equal (fn-otm-jw-frag w es fates) nil))))

(local
 (defthm fn-otm-jw-jlines-append
   (equal (fn-otm-jlines (append a b))
          (append (fn-otm-jlines a) (fn-otm-jlines b)))))

(local
 (defthm fn-otm-jw-take-min-jlines
   (equal (take (min k (len (fn-otm-jlines xs))) (fn-otm-jlines xs))
          (append (fn-otm-jlines (take (fn-otm-jw-cnt (min k (len (fn-otm-jlines xs))) xs) xs))
                  (fn-otm-jw-rest (min k (len (fn-otm-jlines xs))) xs)))
   :hints (("Goal" :use ((:instance fn-otm-jw-take-jlines
                                    (k (min k (len (fn-otm-jlines xs))))))
            :in-theory (disable fn-otm-jw-take-jlines fn-otm-jlines)))))

(local
 (defthm fn-otm-jw-take-its-len-of-append
   (implies (and (true-listp a) (equal n (len a)))
            (equal (take n (append a b)) a))))

(local
 (defthm fn-otm-jw-take-of-its-len
   (implies (and (true-listp f) (equal n (len f)))
            (equal (take n f) f))))

(defthm fn-otm-jw-sim-file
  (implies (and (true-listp file)
                (or (fn-otm-jw-closed w) (equal (fn-otm-jw-offset w) (len file))))
           (equal (mv-nth 1 (fn-otm-jw-sim w file es fates))
                  (append file (fn-otm-jlines (fn-otm-jw-whole w es fates))
                          (fn-otm-jw-frag w es fates))))
  :hints (("Goal" :induct (fn-otm-jw-sim w file es fates)
           :in-theory (disable fn-otm-jw-plan fn-otm-jlines fn-otm-jw-take-of-append
                               fn-otm-jw-ents min))))

; -----------------------------------------------------------------------------
; The reader over what the writer leaves: whole lines, then a fragment.

(local
 (defthm fn-otm-jw-revonto-twice
   (implies (true-listp x)
            (equal (fn-otm-revonto (fn-otm-revonto x acc) nil)
                   (fn-otm-revonto acc x)))))

(local
 (defthm fn-otm-jw-revonto-nil
   (implies (true-listp x) (equal (fn-otm-revonto nil x) x))))

(local
 (defthm fn-otm-jw-nat-lists-true-listp
   (implies (fn-otm-nat-lists-p x) (true-listp x))
   :rule-classes :forward-chaining))

(defthm fn-otm-jw-read-of-lines-then-frag
  (implies (and (fn-otm-nat-lists-p xs) (fn-otm-jw-fragp frag nil))
           (and (equal (fn-otm-journal-read (append (fn-otm-jlines xs) frag)) xs)
                (not (equal (mv-nth 0 (fn-otm-jparse (append (fn-otm-jlines xs) frag) nil nil nil))
                            :malformed))))
  :hints (("Goal" :in-theory (e/d (fn-otm-journal-read) (fn-otm-jlines))
           :use ((:instance fn-otm-jw-jparse-of-frag (xs frag) (acc nil) (fields nil)
                            (entries (fn-otm-revonto xs nil)))))))

(local
 (defthm fn-otm-jw-nat-lists-p-append
   (implies (fn-otm-nat-lists-p a)
            (equal (fn-otm-nat-lists-p (append a b)) (fn-otm-nat-lists-p b)))))

(local
 (defthm fn-otm-jw-nat-lists-p-take
   (implies (and (fn-otm-nat-lists-p a) (<= (nfix n) (len a)))
            (fn-otm-nat-lists-p (take n a)))
   :hints (("Goal" :in-theory (enable take)))))

(defthm fn-otm-jw-whole-nat-lists
  (implies (fn-otm-nat-lists-p es)
           (fn-otm-nat-lists-p (fn-otm-jw-whole w es fates)))
  :hints (("Goal" :in-theory (disable fn-otm-jlines min))))

(defthm fn-otm-jw-frag-is-a-fragment
  (fn-otm-jw-fragp (fn-otm-jw-frag w es fates) nil))

; -----------------------------------------------------------------------------
; The replay of what landed whole: the offered entries up to the first loss,
; then nothing or the mark.

(defun fn-otm-jw-pm-p (x es)
  ; X is a prefix of ES, then nothing or the mark (before an entry of ES)
  (declare (xargs :guard t))
  (cond ((atom x) t)
        ((equal (car x) *fn-otm-mark-entry*) (consp es))
        ((consp es) (and (equal (car x) (car es)) (fn-otm-jw-pm-p (cdr x) (cdr es))))
        (t nil)))

(defun fn-otm-jw-pm-len (x es)
  (declare (xargs :guard t))
  (cond ((atom x) 0)
        ((equal (car x) *fn-otm-mark-entry*) 0)
        ((and (consp es) (equal (car x) (car es))) (+ 1 (fn-otm-jw-pm-len (cdr x) (cdr es))))
        (t 0)))

(local
 (defthm fn-otm-jw-take-small
   (and (equal (take 0 x) nil)
        (implies (consp x) (equal (take 1 x) (list (car x))))
        (implies (and (consp x) (consp (cdr x))) (equal (take 2 x) (list (car x) (cadr x)))))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-otm-jw-cnt-of-ents
   (<= (fn-otm-jw-cnt k (fn-otm-jw-ents w e)) (if (fn-otm-jw-owe w) 2 1))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-otm-jw-cnt-bound (xs (fn-otm-jw-ents w e))))
            :in-theory (disable fn-otm-jw-cnt-bound fn-otm-jw-cnt)))))

(local
 (defthm fn-otm-jw-take-ents-mark
   (implies (and (fn-otm-jw-owe w)
                 (consp (take (fn-otm-jw-cnt k (fn-otm-jw-ents w e)) (fn-otm-jw-ents w e))))
            (equal (car (take (fn-otm-jw-cnt k (fn-otm-jw-ents w e)) (fn-otm-jw-ents w e)))
                   *fn-otm-mark-entry*))
   :hints (("Goal" :in-theory (disable fn-otm-jw-cnt)
            :cases ((equal (fn-otm-jw-cnt k (fn-otm-jw-ents w e)) 0)
                    (equal (fn-otm-jw-cnt k (fn-otm-jw-ents w e)) 1)
                    (equal (fn-otm-jw-cnt k (fn-otm-jw-ents w e)) 2))))))

(local
 (defthm fn-otm-jw-take-ents-pm
   (implies (consp es)
            (fn-otm-jw-pm-p (take (fn-otm-jw-cnt k (fn-otm-jw-ents w (car es)))
                                  (fn-otm-jw-ents w (car es)))
                            es))
   :hints (("Goal" :in-theory (disable fn-otm-jw-cnt)
            :cases ((equal (fn-otm-jw-cnt k (fn-otm-jw-ents w (car es))) 0)
                    (equal (fn-otm-jw-cnt k (fn-otm-jw-ents w (car es))) 1)
                    (equal (fn-otm-jw-cnt k (fn-otm-jw-ents w (car es))) 2))))))

(local
 (defthm fn-otm-jw-append-ents
   (equal (append (fn-otm-jw-ents w e) x)
          (if (fn-otm-jw-owe w)
              (cons *fn-otm-mark-entry* (cons e x))
            (cons e x)))))

(defthm fn-otm-jw-whole-shape
  (let ((x (fn-otm-jw-whole w es fates)))
    (and (implies (fn-otm-jw-owe w)
                  (or (atom x) (equal (car x) *fn-otm-mark-entry*)))
         (fn-otm-jw-pm-p x es)))
  :hints (("Goal" :induct (fn-otm-jw-whole w es fates)
           :in-theory (disable fn-otm-jlines min fn-otm-jw-cnt fn-otm-jw-ents))))

(defthm fn-otm-jw-replay-append
  (equal (fn-otm-replay r (append a b))
         (if (equal (mv-nth 0 (fn-otm-replay r a)) :agrees)
             (fn-otm-replay (mv-nth 1 (fn-otm-replay r a)) b)
           (fn-otm-replay r a)))
  :hints (("Goal" :induct (fn-otm-replay r a)
           :expand ((fn-otm-replay r (append a b)) (fn-otm-replay r a) (fn-otm-replay r nil))
           :in-theory (e/d (fn-otm-replay)
                           (fn-otm-disk-event fn-otm-disk-event-unfolds fn-otm-note fn-otm-init
                            fn-otm-jseq fn-otm-kind-of-op fn-otm-word-code nth nat-listp len)))))

(local
 (defthm fn-otm-jw-replay-of-mark
   (equal (fn-otm-replay s (cons *fn-otm-mark-entry* rest))
          (mv (list :gap (+ 1 (fn-otm-jseq s))) s))
   :hints (("Goal" :expand ((fn-otm-replay s (cons *fn-otm-mark-entry* rest)))))))

(local
 (defthm fn-otm-jw-pm-decomp
   (implies (and (fn-otm-jw-pm-p x es) (true-listp x))
            (and (equal (append (take (fn-otm-jw-pm-len x es) es)
                                (nthcdr (fn-otm-jw-pm-len x es) x))
                        x)
                 (<= (fn-otm-jw-pm-len x es) (len es))
                 (implies (consp (nthcdr (fn-otm-jw-pm-len x es) x))
                          (and (equal (car (nthcdr (fn-otm-jw-pm-len x es) x))
                                      *fn-otm-mark-entry*)
                               (< (fn-otm-jw-pm-len x es) (len es))))))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-otm-jw-append-take-nthcdr
   (implies (<= (nfix m) (len es))
            (equal (append (take m es) (nthcdr m es)) es))
   :hints (("Goal" :in-theory (enable take)))))

(defthm fn-otm-jw-replay-of-prefix-agrees
  (implies (and (equal (mv-nth 0 (fn-otm-replay r es)) :agrees)
                (<= (nfix m) (len es)))
           (equal (mv-nth 0 (fn-otm-replay r (take m es))) :agrees))
  :hints (("Goal" :use ((:instance fn-otm-jw-replay-append (a (take m es)) (b (nthcdr m es))))
           :in-theory (disable fn-otm-jw-replay-append))))

(local
 (defthm fn-otm-jw-replay-nil
   (implies (atom g) (equal (fn-otm-replay s g) (mv :agrees s)))
   :hints (("Goal" :expand ((fn-otm-replay s g))))))

(local
 (defthm fn-otm-jw-replay-prefix-then
   (implies (and (equal (mv-nth 0 (fn-otm-replay r p)) :agrees)
                 (or (atom g) (equal (car g) *fn-otm-mark-entry*)))
            (equal (mv-nth 0 (fn-otm-replay r (append p g)))
                   (if (consp g)
                       (list :gap (+ 1 (fn-otm-jseq (mv-nth 1 (fn-otm-replay r p)))))
                     :agrees)))
   :hints (("Goal" :in-theory (disable binary-append fn-otm-jseq fn-otm-jw-replay-of-mark)
            :use ((:instance fn-otm-jw-replay-of-mark
                             (s (mv-nth 1 (fn-otm-replay r p))) (rest (cdr g))))))))

; What the replay of a pm-shaped list says: agreement, or the gap one past
; the prefix it replayed.
(defthm fn-otm-jw-replay-of-pm
  (implies (and (fn-otm-jw-pm-p x es) (true-listp x)
                (equal (mv-nth 0 (fn-otm-replay r es)) :agrees))
           (equal (mv-nth 0 (fn-otm-replay r x))
                  (if (consp (nthcdr (fn-otm-jw-pm-len x es) x))
                      (list :gap (+ 1 (fn-otm-jseq
                                       (mv-nth 1 (fn-otm-replay
                                                  r (take (fn-otm-jw-pm-len x es) es))))))
                    :agrees)))
  :hints (("Goal" :use ((:instance fn-otm-jw-pm-decomp)
                        (:instance fn-otm-jw-replay-prefix-then
                                   (p (take (fn-otm-jw-pm-len x es) es))
                                   (g (nthcdr (fn-otm-jw-pm-len x es) x)))
                        (:instance fn-otm-jw-replay-of-prefix-agrees
                                   (m (fn-otm-jw-pm-len x es))))
           :in-theory (union-theories '(nfix (:type-prescription fn-otm-jw-pm-len))
                                      (theory 'minimal-theory)))))

(local
 (defthm fn-otm-jw-agreeing-entry-is-next
   (implies (and (equal (mv-nth 0 (fn-otm-replay s (cons e rest))) :agrees)
                 (not (equal (nth 1 e) 0)))
            (equal (car e) (+ 1 (fn-otm-jseq s))))
   :hints (("Goal" :expand ((fn-otm-replay s (cons e rest)))
            :in-theory (disable fn-otm-disk-event fn-otm-note fn-otm-jseq)))))

(local
 (defthm fn-otm-jw-nthcdr-is-cons-nth
   (implies (< (nfix m) (len es))
            (equal (nthcdr m es) (cons (nth m es) (nthcdr (+ 1 (nfix m)) es))))))

; The gap is named by the first sequence number lost: the entry the offered
; list holds at the replayed prefix's end is its successor.
(defthm fn-otm-jw-gap-names-the-first-missing
  (implies (and (equal (mv-nth 0 (fn-otm-replay r es)) :agrees)
                (< (nfix m) (len es))
                (not (equal (nth 1 (nth m es)) 0)))
           (equal (car (nth m es))
                  (+ 1 (fn-otm-jseq (mv-nth 1 (fn-otm-replay r (take m es)))))))
  :hints (("Goal" :use ((:instance fn-otm-jw-replay-append (a (take m es)) (b (nthcdr m es)))
                        (:instance fn-otm-jw-replay-of-prefix-agrees)
                        (:instance fn-otm-jw-agreeing-entry-is-next
                                   (s (mv-nth 1 (fn-otm-replay r (take m es))))
                                   (e (nth m es)) (rest (nthcdr (+ 1 (nfix m)) es)))
                        (:instance fn-otm-jw-append-take-nthcdr)
                        (:instance fn-otm-jw-nthcdr-is-cons-nth))
           :in-theory (union-theories '(nfix) (theory 'minimal-theory)))))

(defthm fn-otm-jw-lost-entry-exists
  (implies (and (fn-otm-jw-pm-p x es) (true-listp x)
                (consp (nthcdr (fn-otm-jw-pm-len x es) x)))
           (< (fn-otm-jw-pm-len x es) (len es)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-otm-jw-pm-decomp))
           :in-theory (disable fn-otm-jw-pm-decomp))))

(local
 (defthm fn-otm-jw-whole-true-listp
   (true-listp (fn-otm-jw-whole w es fates))
   :hints (("Goal" :in-theory (disable fn-otm-jlines min fn-otm-jw-cnt fn-otm-jw-ents)))))

(local
 (defthm fn-otm-jw-read-of-the-writers-file
   (implies (and (fn-otm-nat-lists-p e0) (fn-otm-nat-lists-p x) (fn-otm-jw-fragp frag nil))
            (and (equal (fn-otm-journal-read
                         (append (fn-otm-jlines e0) (append (fn-otm-jlines x) frag)))
                        (append e0 x))
                 (not (equal (mv-nth 0 (fn-otm-jparse
                                        (append (fn-otm-jlines e0) (append (fn-otm-jlines x) frag))
                                        nil nil nil))
                             :malformed))))
   :hints (("Goal" :use ((:instance fn-otm-jw-read-of-lines-then-frag (xs (append e0 x))))
            :in-theory (disable fn-otm-jw-read-of-lines-then-frag fn-otm-jlines
                                fn-otm-journal-read fn-otm-jparse)))))

; The keystone below with the entries typed (natural lists, true lists).
(local
 (defthm fn-otm-jw-file-reads-agrees-or-gap-typed
  (implies (and (fn-otm-nat-lists-p e0) (fn-otm-nat-lists-p es)
                (equal (mv-nth 0 (fn-otm-replay r e0)) :agrees)
                (equal (mv-nth 0 (fn-otm-replay (mv-nth 1 (fn-otm-replay r e0)) es)) :agrees))
           (let* ((w0 (fn-otm-jw-init (len (fn-otm-jlines e0))))
                  (file (mv-nth 1 (fn-otm-jw-sim w0 (fn-otm-jlines e0) es fates)))
                  (x (fn-otm-jw-whole w0 es fates))
                  (m (fn-otm-jw-pm-len x es)))
             (and (not (equal (mv-nth 0 (fn-otm-jparse file nil nil nil)) :malformed))
                  (equal (fn-otm-journal-read file) (append e0 x))
                  (equal (mv-nth 0 (fn-otm-replay r (fn-otm-journal-read file)))
                         (if (consp (nthcdr m x))
                             (list :gap (+ 1 (fn-otm-jseq
                                              (mv-nth 1 (fn-otm-replay
                                                         (mv-nth 1 (fn-otm-replay r e0))
                                                         (take m es))))))
                           :agrees)))))
  :hints (("Goal" :use ((:instance fn-otm-jw-replay-of-pm
                                   (r (mv-nth 1 (fn-otm-replay r e0)))
                                   (x (fn-otm-jw-whole (fn-otm-jw-init (len (fn-otm-jlines e0)))
                                                       es fates)))
                        (:instance fn-otm-jw-whole-shape
                                   (w (fn-otm-jw-init (len (fn-otm-jlines e0))))))
           :in-theory (disable fn-otm-jw-sim fn-otm-jw-whole fn-otm-jw-frag
                               fn-otm-jlines fn-otm-jparse fn-otm-journal-read
                               fn-otm-jw-pm-len fn-otm-jw-pm-p fn-otm-jseq mv-nth
                               fn-otm-jw-replay-of-pm fn-otm-jw-whole-shape)))))

; The corollary below, typed.
(local
 (defthm fn-otm-jw-gap-is-the-first-lost-typed
  (implies (and (fn-otm-nat-lists-p e0) (fn-otm-nat-lists-p es)
                (equal (mv-nth 0 (fn-otm-replay r e0)) :agrees)
                (equal (mv-nth 0 (fn-otm-replay (mv-nth 1 (fn-otm-replay r e0)) es)) :agrees))
           (let* ((w0 (fn-otm-jw-init (len (fn-otm-jlines e0))))
                  (x (fn-otm-jw-whole w0 es fates))
                  (m (fn-otm-jw-pm-len x es)))
             (implies (and (consp (nthcdr m x))
                           (not (equal (nth 1 (nth m es)) 0)))
                      (equal (mv-nth 0 (fn-otm-replay
                                        r (fn-otm-journal-read
                                           (mv-nth 1 (fn-otm-jw-sim w0 (fn-otm-jlines e0) es fates)))))
                             (list :gap (car (nth m es)))))))
  :hints (("Goal" :use ((:instance fn-otm-jw-file-reads-agrees-or-gap-typed)
                        (:instance fn-otm-jw-gap-names-the-first-missing
                                   (r (mv-nth 1 (fn-otm-replay r e0)))
                                   (m (fn-otm-jw-pm-len
                                       (fn-otm-jw-whole (fn-otm-jw-init (len (fn-otm-jlines e0)))
                                                        es fates)
                                       es)))
                        (:instance fn-otm-jw-lost-entry-exists
                                   (x (fn-otm-jw-whole (fn-otm-jw-init (len (fn-otm-jlines e0)))
                                                       es fates)))
                        (:instance fn-otm-jw-whole-shape
                                   (w (fn-otm-jw-init (len (fn-otm-jlines e0)))))
                        (:instance fn-otm-jw-whole-true-listp
                                   (w (fn-otm-jw-init (len (fn-otm-jlines e0))))))
           :in-theory (union-theories '(nfix (:type-prescription fn-otm-jw-pm-len))
                                      (theory 'minimal-theory))))))

;; The entries' being natural lists follows from their replaying to
;; agreement (every entry the replay takes is a natural list of seven), and a
;; list's final cdr changes nothing here: the keystone without them.
(local
 (defthm fn-otm-jw-replay-tlf
   (equal (fn-otm-replay r (true-list-fix xs)) (fn-otm-replay r xs))
   :hints (("Goal" :induct (fn-otm-replay r xs)
            :expand ((fn-otm-replay r (true-list-fix xs)) (fn-otm-replay r xs))
            :in-theory (e/d (fn-otm-replay)
                            (fn-otm-disk-event fn-otm-disk-event-unfolds fn-otm-note fn-otm-init
                             fn-otm-jseq fn-otm-kind-of-op fn-otm-word-code nth nat-listp len))))))

(local
 (defthm fn-otm-jw-agrees-nat-lists
   (implies (equal (mv-nth 0 (fn-otm-replay r xs)) :agrees)
            (fn-otm-nat-lists-p (true-list-fix xs)))
   :hints (("Goal" :induct (fn-otm-replay r xs)
            :expand ((fn-otm-replay r xs))
            :in-theory (e/d (fn-otm-replay)
                            (fn-otm-disk-event fn-otm-disk-event-unfolds fn-otm-note fn-otm-init
                             fn-otm-jseq fn-otm-kind-of-op fn-otm-word-code nth))))))

(local
 (defthm fn-otm-jw-jlines-tlf
   (equal (fn-otm-jlines (true-list-fix xs)) (fn-otm-jlines xs))))

(local
 (defthm fn-otm-jw-sim-tlf
   (equal (fn-otm-jw-sim w file (true-list-fix es) fates) (fn-otm-jw-sim w file es fates))
   :hints (("Goal" :induct (fn-otm-jw-sim w file es fates)
            :in-theory (disable fn-otm-jw-plan fn-otm-jlines min fn-otm-jw-after fn-otm-jw-truncated
                                fn-otm-jw-drop fn-otm-jw-fate-ok fn-otm-jw-fate-k fn-otm-jw-fate-tok
                                take fn-otm-jline len binary-append fn-otm-jw-after-facts)))))

(local
 (defthm fn-otm-jw-whole-tlf
   (equal (fn-otm-jw-whole w (true-list-fix es) fates) (fn-otm-jw-whole w es fates))
   :hints (("Goal" :induct (fn-otm-jw-whole w es fates)
            :in-theory (disable fn-otm-jlines min fn-otm-jw-cnt fn-otm-jw-ents)))))

(local
 (defthm fn-otm-jw-pm-len-tlf
   (equal (fn-otm-jw-pm-len x (true-list-fix es)) (fn-otm-jw-pm-len x es))))

(local
 (defthm fn-otm-jw-take-tlf
   (equal (take m (true-list-fix es)) (take m es))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm fn-otm-jw-append-tlf
   (equal (append (true-list-fix a) b) (append a b))))

(local
 (defthm fn-otm-jw-nth-tlf
   (equal (nth m (true-list-fix es)) (nth m es))))

; KEYSTONE (PKT-872, PRF-360).  The subjects are the host's calls
; fn-otm-jw-init, fn-otm-jw-plan, fn-otm-jw-after, fn-otm-jw-truncated and
; fn-otm-jw-drop (host/native/owner.lisp fnn-owner-journal-open;
; host/native/io.lisp fnn-journal-write, called by fnn-log-writer-loop),
; composed by fn-otm-jw-sim over ANY fates, and the reader and replay of the
; operator's `store ROOT journal' (fn-otm-journal-report: fn-otm-jparse,
; fn-otm-journal-read, fn-otm-replay).  From a file of whole lines E0 (what
; the open's cut leaves), whatever happens to each offered entry -- and so
; at every process-death cut and every ENOSPC -- the file reads back with no
; malformed line, as E0 and the entries that landed whole, and replays to
; agreement or to the gap one past the last entry replayed.
(defthm fn-otm-jw-file-reads-agrees-or-gap
  (implies (and (equal (mv-nth 0 (fn-otm-replay r e0)) :agrees)
                (equal (mv-nth 0 (fn-otm-replay (mv-nth 1 (fn-otm-replay r e0)) es)) :agrees))
           (let* ((w0 (fn-otm-jw-init (len (fn-otm-jlines e0))))
                  (file (mv-nth 1 (fn-otm-jw-sim w0 (fn-otm-jlines e0) es fates)))
                  (x (fn-otm-jw-whole w0 es fates))
                  (m (fn-otm-jw-pm-len x es)))
             (and (not (equal (mv-nth 0 (fn-otm-jparse file nil nil nil)) :malformed))
                  (equal (fn-otm-journal-read file) (append e0 x))
                  (equal (mv-nth 0 (fn-otm-replay r (fn-otm-journal-read file)))
                         (if (consp (nthcdr m x))
                             (list :gap (+ 1 (fn-otm-jseq
                                              (mv-nth 1 (fn-otm-replay
                                                         (mv-nth 1 (fn-otm-replay r e0))
                                                         (take m es))))))
                           :agrees)))))
  :hints (("Goal" :use ((:instance fn-otm-jw-file-reads-agrees-or-gap-typed
                                   (e0 (true-list-fix e0)) (es (true-list-fix es)))
                        (:instance fn-otm-jw-agrees-nat-lists (xs e0))
                        (:instance fn-otm-jw-agrees-nat-lists
                                   (r (mv-nth 1 (fn-otm-replay r e0))) (xs es)))
           :in-theory (disable fn-otm-jw-file-reads-agrees-or-gap-typed fn-otm-jw-agrees-nat-lists
                               fn-otm-jw-sim fn-otm-jw-whole fn-otm-jw-frag
                               fn-otm-jlines fn-otm-jparse fn-otm-journal-read
                               fn-otm-jw-pm-len fn-otm-jw-pm-p fn-otm-jseq fn-otm-jw-init
                               true-list-fix))))

; ... and the N of that gap is the sequence number of the first entry lost
; (the offered entry at the replayed prefix's end), unless that entry is a
; start (then the gap is one past the previous segment's last entry).
(defthm fn-otm-jw-gap-is-the-first-lost
  (implies (and (equal (mv-nth 0 (fn-otm-replay r e0)) :agrees)
                (equal (mv-nth 0 (fn-otm-replay (mv-nth 1 (fn-otm-replay r e0)) es)) :agrees))
           (let* ((w0 (fn-otm-jw-init (len (fn-otm-jlines e0))))
                  (x (fn-otm-jw-whole w0 es fates))
                  (m (fn-otm-jw-pm-len x es)))
             (implies (and (consp (nthcdr m x))
                           (not (equal (nth 1 (nth m es)) 0)))
                      (equal (mv-nth 0 (fn-otm-replay
                                        r (fn-otm-journal-read
                                           (mv-nth 1 (fn-otm-jw-sim w0 (fn-otm-jlines e0) es fates)))))
                             (list :gap (car (nth m es)))))))
  :hints (("Goal" :use ((:instance fn-otm-jw-gap-is-the-first-lost-typed
                                   (e0 (true-list-fix e0)) (es (true-list-fix es)))
                        (:instance fn-otm-jw-agrees-nat-lists (xs e0))
                        (:instance fn-otm-jw-agrees-nat-lists
                                   (r (mv-nth 1 (fn-otm-replay r e0))) (xs es)))
           :in-theory (disable fn-otm-jw-gap-is-the-first-lost-typed fn-otm-jw-agrees-nat-lists
                               fn-otm-jw-sim fn-otm-jw-whole fn-otm-jw-frag
                               fn-otm-jlines fn-otm-jparse fn-otm-journal-read
                               fn-otm-jw-pm-len fn-otm-jw-pm-p fn-otm-jseq fn-otm-jw-init
                               true-list-fix nth mv-nth fn-otm-jw-sim-file
                               fn-otm-jw-replay-append fn-otm-jw-read-of-the-writers-file))))

; A run's segment as the host offers it: the start entry
; (fn-otm-start-line's) and then the run's entries replay to agreement from
; any state, so the keystone applies to every segment the host writes.
(defun fn-otm-jw-start-entry (reading wall)
  (declare (xargs :guard t))
  (list 0 0 (nfix reading) (nfix wall) 0 0 0))

(defthm fn-otm-jw-start-line-is-the-start-entry
  (equal (fn-otm-start-line reading wall)
         (fn-otm-jline (fn-otm-jw-start-entry reading wall)))
  :hints (("Goal" :in-theory (enable fn-otm-start-line))))

(defthm fn-otm-jw-segment-agrees
  (implies (fn-otm-run-okp steps)
           (let ((es (cons (fn-otm-jw-start-entry reading wall)
                           (mv-nth 0 (fn-otm-run (fn-otm-init) steps)))))
             (and (fn-otm-nat-lists-p es)
                  (equal (mv-nth 0 (fn-otm-replay s es)) :agrees))))
  :hints (("Goal" :use ((:instance fn-otm-journal-determines-the-decisions (s (fn-otm-init)))
                        (:instance fn-otm-journal-read-of-jlines
                                   (es (mv-nth 0 (fn-otm-run (fn-otm-init) steps))))
                        (:instance fn-otm-run-entries-shape (s (fn-otm-init))))
           :expand ((fn-otm-replay s (cons (fn-otm-jw-start-entry reading wall)
                                           (mv-nth 0 (fn-otm-run (fn-otm-init) steps)))))
           :in-theory (e/d (fn-otm-replay)
                           (fn-otm-journal-determines-the-decisions fn-otm-journal-read-of-jlines
                            fn-otm-run-entries-shape
                            fn-otm-run fn-otm-init (:e fn-otm-init) (:e fn-otm-run) fn-otm-jlines
                            fn-otm-journal-read fn-otm-jparse fn-otm-run-okp
                            fn-otm-disk-event fn-otm-note)))))

; -----------------------------------------------------------------------------
; The open's cut.

(local
 (defthm fn-otm-jw-lf-pos-append
   (equal (fn-otm-jw-lf-pos (append a b))
          (if (fn-otm-jw-lf-pos b)
              (+ (len a) (fn-otm-jw-lf-pos b))
            (fn-otm-jw-lf-pos a)))))

(defun fn-otm-jw-no-lf-p (xs)
  (declare (xargs :guard t))
  (if (consp xs) (and (not (eql (car xs) 10)) (fn-otm-jw-no-lf-p (cdr xs))) t))

(local
 (defthm fn-otm-jw-lf-pos-of-no-lf
   (implies (fn-otm-jw-no-lf-p xs) (equal (fn-otm-jw-lf-pos xs) nil))))

(local
 (defthm fn-otm-jw-no-lf-p-append
   (equal (fn-otm-jw-no-lf-p (append a b))
          (and (fn-otm-jw-no-lf-p a) (fn-otm-jw-no-lf-p b)))))

(local
 (defthm fn-otm-jw-no-lf-p-when-no-pos
   (implies (not (fn-otm-jw-lf-pos xs)) (fn-otm-jw-no-lf-p xs))))

(local
 (defthm fn-otm-jw-fragp-no-lf
   (implies (fn-otm-jw-fragp xs accp) (fn-otm-jw-no-lf-p xs))))

(local
 (defthm fn-otm-jw-lf-pos-of-atom-len
   (implies (equal (len a) 0) (equal (fn-otm-jw-lf-pos a) nil))))

; The step's contract, the invariant of the host's backward read: with the
; file's octets after the chunk holding no LF (true of the first chunk,
; which ends the file, and kept by every :more), a :cut is the whole file's
; cut, and after a :more the octets after the next chunk hold no LF.
(defthm fn-otm-jw-open-step-is-the-cut
  (implies (and (equal file (append a (append chunk post)))
                (equal start (len a))
                (fn-otm-jw-no-lf-p post))
           (and (implies (equal (car (fn-otm-jw-open-step chunk start)) :cut)
                         (equal (cadr (fn-otm-jw-open-step chunk start))
                                (fn-otm-jw-open-cut file)))
                (implies (equal (car (fn-otm-jw-open-step chunk start)) :more)
                         (fn-otm-jw-no-lf-p (append chunk post))))))

(local
 (defthm fn-otm-jw-digits-no-lf
   (implies (fn-otm-jw-digitsp xs) (equal (fn-otm-jw-lf-pos xs) nil))))

(local
 (defthm fn-otm-jw-lf-pos-jline
   (equal (fn-otm-jw-lf-pos (fn-otm-jline ns))
          (if (consp ns) (len (fn-otm-jline ns)) nil))))

(local
 (defthm fn-otm-jw-lf-pos-jlines
   (equal (fn-otm-jw-lf-pos (fn-otm-jlines xs))
          (if (consp (fn-otm-jlines xs)) (len (fn-otm-jlines xs)) nil))))

; The cut of a file the writer left (whole lines, then a fragment) is its
; whole lines: the open resumes appending right after the last whole entry.
(defthm fn-otm-jw-open-cut-of-a-written-file
  (implies (fn-otm-jw-fragp frag nil)
           (equal (fn-otm-jw-open-cut (append (fn-otm-jlines xs) frag))
                  (len (fn-otm-jlines xs))))
  :hints (("Goal" :in-theory (disable fn-otm-jlines))))


; The host's backward read over a file the writer left cuts exactly its
; whole lines: every :cut fn-otm-jw-open-step answers under the read's
; invariant is the length of the whole lines (host/native/owner.lisp
; fnn-owner-journal-cut calls fn-otm-jw-open-step).
(defthm fn-otm-jw-open-step-cuts-a-written-file
  (implies (and (fn-otm-jw-fragp frag nil)
                (equal (append (fn-otm-jlines xs) frag) (append a (append chunk post)))
                (equal start (len a))
                (fn-otm-jw-no-lf-p post)
                (equal (car (fn-otm-jw-open-step chunk start)) :cut))
           (equal (cadr (fn-otm-jw-open-step chunk start))
                  (len (fn-otm-jlines xs))))
  :hints (("Goal" :use ((:instance fn-otm-jw-open-step-is-the-cut
                                   (file (append (fn-otm-jlines xs) frag)))
                        (:instance fn-otm-jw-open-cut-of-a-written-file))
           :in-theory (disable fn-otm-jw-open-step-is-the-cut fn-otm-jw-open-cut-of-a-written-file
                               fn-otm-jw-open-step fn-otm-jw-open-cut fn-otm-jlines))))
(in-theory (disable fn-otm-jw-sim fn-otm-jw-whole fn-otm-jw-frag))
