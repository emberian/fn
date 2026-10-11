; fn: a read opens no log segment longer than the extent its heap was
; decided over (Builder A; seam 2b with Builder M; retires the named adapter
; MEMORY-OBSERVED-EXTENT-CAP).
;
; The heap probe (host/native/heap.lisp fnn-command-heap, the launcher's
; `heap -- ARGV') decides a store-opening command's heap over the observed
; totals (books/heap-command.lisp fn-mo-observed-totals HDR SUFFIX EXTENT),
; whose LOG is at least EXTENT, the largest journal/ segment's lstat size the
; probe's walk saw (fnn-heap-charged-totals); every entry the open reads from
; a segment no longer than EXTENT is within that LOG (KEYSTONE
; fn-mo-observed-log-holds-every-entry-read, books/heap-command-entry-scratch).
; The probe and the command are two processes and the store may grow between
; them, so the probe prints EXTENT on its decision line (fn-lxc-command-line:
; ` extent=E' exactly when the decision is the observed branch), the
; launcher (packaging/fn fn_decide_heap) exports it as FN_LOG_EXTENT_CAP, and
; the command reads it once per segment (host/native/io.lisp
; fnn-log-observed-extent): a segment longer than the cap is refused by name
; before any of its entries is read (fn-lxc-verdict), and the descriptor's
; size is checked equal to that admitted size at its open
; (fnn-log-open-segment).  The reader then reads within the admitted size,
; whatever the file does after: every entry ends within it (KEYSTONE
; fn-lxc-admitted-entries-end-within-the-admitted-size), so no entry past the
; decided extent is read.  A file that grows after its descriptor is checked
; is still read, but only within that frozen size (Codex review-cap item 4).
; Scope: the two entry readers of the log stream; the genesis file's bounded
; metadata read, the rotation's bounded zero scan and the explicit-extent
; `log' diagnostics are outside it.  A start whose caller names its own heap
; (SBCL_USER_ARGS --dynamic-space-size, FN_TEST_HEAP_MB) runs no probe, and
; the launcher leaves FN_LOG_EXTENT_CAP as the caller set it: unset, the read
; is :uncapped; set, it is the caller's own cap (the native test of the
; refusal uses this).
(in-package "ACL2")
(include-book "heap-command-entry-scratch")
(include-book "decimal-text")
(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; THE PROBE'S WORDS.  CLASS is the command's (fn-heap-command-growth); the
; words are present exactly when fn-heap-command-decide takes its observed
; branch (a store-opening class, fn-mo-read-observed-p) and EXTENT is the
; observation's.
(defun fn-lxc-capped-p (class totals img config-octets card extent)
  (declare (xargs :guard t))
  (and (fn-mo-store-opening-p class)
       (fn-mo-read-observed-p totals img config-octets card)
       (natp extent)))

(defun fn-lxc-words (class totals img config-octets card extent)
  (declare (xargs :guard t))
  (if (fn-lxc-capped-p class totals img config-octets card extent)
      (concatenate 'string " extent=" (fn-decimal-text extent))
    ""))

; The probe's whole line: the decision's (fn-heap-command-line) and the
; words.
(defun fn-lxc-command-line (decision action command replayp totals img config-octets card extent)
  (declare (xargs :guard t))
  (concatenate 'string
               (fn-heap-command-line decision action command replayp totals img config-octets card)
               (fn-lxc-words (fn-heap-command-growth action command replayp)
                             totals img config-octets card extent)))

; -----------------------------------------------------------------------------
; THE COMMAND'S CAP: the text of FN_LOG_EXTENT_CAP as the process finds it
; (NIL: unset).  Unset is :uncapped; a nonempty run of decimal digits is
; that natural; anything else is :unreadable, which refuses every segment.
(defun fn-lxc-digits-value (chars acc)
  (declare (xargs :guard (natp acc)))
  (if (consp chars)
      (let ((c (car chars)))
        (if (and (characterp c) (digit-char-p c))
            (fn-lxc-digits-value (cdr chars) (+ (* 10 acc) (digit-char-p c)))
          nil))
    acc))

(defun fn-lxc-cap-of-text (text)
  (declare (xargs :guard t))
  (cond ((null text) :uncapped)
        ((and (stringp text) (< 0 (length text)))
         (or (fn-lxc-digits-value (coerce text 'list) 0) :unreadable))
        (t :unreadable)))

; -----------------------------------------------------------------------------
; THE VERDICT at a segment's open, on its observed SIZE, before any entry.
(defun fn-lxc-verdict (size cap)
  (declare (xargs :guard t))
  (cond ((equal cap :uncapped) :read)
        ((and (natp cap) (natp size) (<= size cap)) :read)
        (t :refused)))

(defun fn-lxc-refusal-text (name size cap)
  (declare (xargs :guard t))
  (if (natp cap)
      (concatenate 'string "log segment " (if (stringp name) name "?") " is "
                   (fn-decimal-text size)
                   " octets, past the extent " (fn-decimal-text cap)
                   " the heap probe decided this read's memory over"
                   " (log-segment-past-decided-extent)")
    "FN_LOG_EXTENT_CAP is not a decimal extent (log-extent-cap-unreadable)"))

; -----------------------------------------------------------------------------
; The round trip: the cap a command reads from the probe's words is the
; probe's extent.
(local
 (defun fn-lxc-digits (n)
   (if (zp n)
       nil
     (append (fn-lxc-digits (floor n 10)) (list (digit-to-char (mod n 10)))))))

(local
 (defthm fn-lxc-explode-is-digits
   (implies (natp n)
            (equal (explode-nonnegative-integer n 10 ans)
                   (if (and (zp n) (null ans))
                       '(#\0)
                     (append (fn-lxc-digits n) ans))))))

;; A digit's value is a natural (the type the fold's accumulator keeps).
(local
 (defthm fn-lxc-digit-char-p-natp
   (or (null (digit-char-p c)) (natp (digit-char-p c)))
   :rule-classes :type-prescription))

(local
 (defthm fn-lxc-digits-value-of-append
   (implies (natp acc)
            (equal (fn-lxc-digits-value (append x y) acc)
                   (let ((v (fn-lxc-digits-value x acc)))
                     (and v (fn-lxc-digits-value y v)))))
   :hints (("Goal" :induct (fn-lxc-digits-value x acc)
                   :in-theory (disable (tau-system) digit-char-p)))))

(local
 (defthm fn-lxc-digit-of-digit-to-char
   (implies (and (natp d) (< d 10))
            (equal (digit-char-p (digit-to-char d)) d))))

(local
 (defthm fn-lxc-digits-value-of-digits
   (equal (fn-lxc-digits-value (fn-lxc-digits n) 0) (nfix n))
   :hints (("Goal" :induct (fn-lxc-digits n)
                   :in-theory (disable digit-to-char digit-char-p (tau-system)))
           ("Subgoal *1/2" :use ((:instance fn-lxc-digit-of-digit-to-char (d (mod n 10)))
                                 (:instance floor-mod-elim (x n) (y 10)))))))

(local
 (defthm fn-lxc-digits-chars
   (character-listp (fn-lxc-digits n))
   :hints (("Goal" :induct (fn-lxc-digits n) :in-theory (disable digit-to-char)))))

(local
 (defthm fn-lxc-digits-consp
   (implies (posp n) (consp (fn-lxc-digits n)))
   :hints (("Goal" :expand ((fn-lxc-digits n)) :in-theory (disable digit-to-char)))))

(defthm fn-lxc-cap-of-the-probes-extent
  (implies (natp extent)
           (equal (fn-lxc-cap-of-text (fn-decimal-text extent)) extent))
  :hints (("Goal" :in-theory (e/d (fn-decimal-text fn-lxc-cap-of-text)
                                  (fn-lxc-digits-value fn-lxc-digits explode-nonnegative-integer
                                   digit-to-char))
                  :cases ((posp extent)))))

; -----------------------------------------------------------------------------
; KEYSTONE: under the cap the probe decided over, every entry the open reads
; from a segment it admits -- the stream's (fn-lgw-entry-len-bounded) and
; the damage probe's (fn-lgdm-entry-len-bounded) -- is within the
; observation's LOG.
(local
 (defthm fn-lxc-lgdm-entry-within-size
   (<= (nfix (fn-lgdm-entry-len-bounded h ps size max)) (nfix size))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-lgdm-entry-len-bounded fn-lgdm-entry-len)
                                   ((tau-system) fn-lg-entry-len-bound fn-lg-declared-len))))))

(local
 (defthm fn-lxc-observed-log-at-least-cap
   (implies (fn-mo-observed-totals hdr suffix cap)
            (<= cap (fn-mm-tot-log (fn-mo-observed-totals hdr suffix cap))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-mo-observed-totals fn-mo-tot-log-at-least)))))

(local
 (defthm fn-lxc-observed-cap-natp
   (implies (fn-mo-observed-totals hdr suffix cap) (natp cap))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-mo-observed-totals)))))

(defthm fn-lxc-admitted-segment-entries-within-the-decided-log
  (implies (and (fn-mo-observed-totals hdr suffix cap)
                (equal (fn-lxc-verdict size cap) :read))
           (and (<= (nfix (fn-lgw-entry-len-bounded h st size max))
                    (fn-mm-tot-log (fn-mo-observed-totals hdr suffix cap)))
                (<= (nfix (fn-lgdm-entry-len-bounded h ps size max))
                    (fn-mm-tot-log (fn-mo-observed-totals hdr suffix cap)))))
  :hints (("Goal" :in-theory (union-theories '(fn-lxc-verdict natp nfix) (theory 'minimal-theory))
                  :use ((:instance fn-mo-observed-log-holds-every-entry-read
                                   (extent cap) (segment-extent size))
                        fn-lxc-lgdm-entry-within-size
                        fn-lxc-observed-log-at-least-cap
                        fn-lxc-observed-cap-natp))))

; KEYSTONE (the frozen read range): every entry either reader takes from an
; admitted segment ends within the admitted size, which is at most the cap.
(local
 (defthm fn-lxc-lgw-entry-ends-within-size
   (implies (fn-lgw-entry-len-bounded h st size max)
            (<= (+ (fn-lgw-pos st) (fn-lgw-entry-len-bounded h st size max)) (nfix size)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-lgw-entry-len-bounded fn-lgw-entry-len)
                                   ((tau-system) fn-lg-entry-len-bound fn-lg-declared-len))))))

(local
 (defthm fn-lxc-lgdm-entry-ends-within-size
   (implies (fn-lgdm-entry-len-bounded h ps size max)
            (<= (+ (fn-lgdm-q ps) (fn-lgdm-entry-len-bounded h ps size max)) (nfix size)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-lgdm-entry-len-bounded fn-lgdm-entry-len)
                                   ((tau-system) fn-lg-entry-len-bound fn-lg-declared-len))))))

(defthm fn-lxc-admitted-entries-end-within-the-admitted-size
  (implies (and (natp cap) (equal (fn-lxc-verdict size cap) :read))
           (and (<= size (nfix cap))
                (implies (fn-lgw-entry-len-bounded h st size max)
                         (<= (+ (fn-lgw-pos st) (fn-lgw-entry-len-bounded h st size max)) size))
                (implies (fn-lgdm-entry-len-bounded h ps size max)
                         (<= (+ (fn-lgdm-q ps) (fn-lgdm-entry-len-bounded h ps size max)) size))))
  :hints (("Goal" :in-theory (union-theories '(fn-lxc-verdict natp nfix) (theory 'minimal-theory))
                  :use (fn-lxc-lgw-entry-ends-within-size fn-lxc-lgdm-entry-ends-within-size))))

; The refusals: a segment past a natural cap, and every segment under an
; unreadable one.
(defthm fn-lxc-verdict-refuses-past-the-cap
  (implies (and (natp cap) (natp size) (< cap size))
           (equal (fn-lxc-verdict size cap) :refused)))

(defthm fn-lxc-verdict-refuses-an-unreadable-cap
  (equal (fn-lxc-verdict size :unreadable) :refused))
