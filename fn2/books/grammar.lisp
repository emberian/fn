; The command-grammar DSL (layer-D brief contract item 2; D2a). A wire
; grammar is declared once with DEFGRAMMAR; from the declaration come the
; command-tag and reply-tag enums, one (:command NAME) declaration row per
; entry, the keyword matcher, the per-command argument parsers, the state
; and block/hand-off tables, the reply catalogue and its typed renderer, the
; transcript runner (the logical view the fragmentation statement is over)
; and the grammar's owed obligations. The runtime here is generic and
; scalar: bytes are read and written in pool slots through the pool's own
; checked exports, a line or token is an (offset, length) in its slot, and
; nothing on a served path builds a list of octets.
(in-package "ACL2")
(include-book "pool-ranges")
(include-book "std/util/bstar" :dir :system)
(fn2-book-layer :d)

(make-event (value (fn2-declare '(:operation-set fn2-grammar) nil nil nil)))

(defconst *fn2-gram-lf* 10)
(defconst *fn2-gram-cr* 13)
(defconst *fn2-gram-sp* 32)
(defconst *fn2-gram-tab* 9)
(defconst *fn2-gram-dot* 46)
(defconst *fn2-gram-dash* 45)
(defconst *fn2-gram-comma* 44)
(defconst *fn2-gram-bang* 33)
(defconst *fn2-gram-lt* 60)
(defconst *fn2-gram-gt* 62)
; The largest NNTP article number (RFC 3977 section 6), and the run quantum.
(defconst *fn2-gram-article-max* 2147483647)
(defconst *fn2-gram-run-bytes* 4096)
; Template field markers, compiled from a reply text's field words.
(defconst *fn2-gram-field-number* 1)
(defconst *fn2-gram-field-span* 2)
(defconst *fn2-gram-field-digits14* 3)

; ------------------------------------------------------------------------
; Checked byte access. A read that the pool refuses is reported, never
; replaced by a value; the byte is in 0..255 by construction.
(defun fn2-gram-read (slot gen idx okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (mv-let (code byte) (fn2-pool-read slot gen idx okind oslot ogen fn2-pool)
    (if (and (eq code :ok) (natp byte) (< byte 256)) (mv t byte) (mv nil 0))))
(defthm fn2-gram-read-byte
  (and (natp (mv-nth 1 (fn2-gram-read slot gen idx okind oslot ogen fn2-pool)))
       (< (mv-nth 1 (fn2-gram-read slot gen idx okind oslot ogen fn2-pool)) 256))
  :rule-classes ((:type-prescription :corollary
                  (natp (mv-nth 1 (fn2-gram-read slot gen idx okind oslot ogen fn2-pool))))
                 (:linear :corollary
                  (< (mv-nth 1 (fn2-gram-read slot gen idx okind oslot ogen fn2-pool)) 256))))
(in-theory (disable fn2-gram-read))

(defun fn2-gram-fill (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (nfix (fn2-pool-fill slot fn2-pool)) 0))
(defthm fn2-gram-fill-natp (natp (fn2-gram-fill slot fn2-pool)) :rule-classes :type-prescription)
(in-theory (disable fn2-gram-fill))

; ------------------------------------------------------------------------
; The line framer: a bounded continuation over [pos, fill) of one slot.
; State is three scalars: START (the retained line's first octet), POS (the
; next octet to examine) and OVERFLOW (1 once the current line exceeded
; CAP; its octets are then not retained: START follows POS). LEFT is the
; run's byte budget. Status, by name:
;   :line       [start, pos) is one line, its LF at pos-1, within CAP;
;   :long-line  an over-cap line has ended (the caller refuses it);
;   :overflow   the current line just exceeded CAP (a command line is then
;               refused; a block line is followed to its LF);
;   :need-more  every filled octet is examined; retained [start, pos);
;   :budget     LEFT is spent; resume with the returned state;
;   :fault      the pool refused a read of a filled octet.
(defun fn2-gram-frame (left start pos overflow cap slot gen okind oslot ogen fn2-pool)
  ; D2c: one fn2-pool-scan for LF over [pos, pos+n), n = min(LEFT, fill-pos),
  ; replacing the octet loop. The overflow point is the first octet at or
  ; after POS that would make the line reach CAP without its LF:
  ; max(pos, start+cap-1).
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp start) (natp pos)
                              (<= start pos) (bitp overflow) (posp cap))))
  (let ((nfill (fn2-gram-fill slot fn2-pool)) (pos (nfix pos)) (left (nfix left)))
    (cond ((zp left) (mv :budget start pos overflow))
          ((>= pos nfill) (mv :need-more start pos overflow))
          (t (let ((n (min left (- nfill pos))))
               (mv-let (code at) (fn2-pool-scan slot gen pos n *fn2-gram-lf* okind oslot ogen fn2-pool)
                 (if (not (eq code :ok)) (mv :fault start pos overflow)
                   (let* ((at (nfix at)) (lf (+ pos at)) (found (< at n)))
                     (if (equal overflow 1)
                         (cond (found (mv :long-line (+ 1 lf) (+ 1 lf) 1))
                               ((equal n left) (mv :budget (+ pos n) (+ pos n) 1))
                               (t (mv :need-more nfill nfill 1)))
                       (let ((limit (max pos (+ (nfix start) (nfix cap) -1))))
                         (cond ((and found (<= lf limit)) (mv :line start (+ 1 lf) overflow))
                               ((< limit (+ pos n)) (mv :overflow (+ 1 limit) (+ 1 limit) 1))
                               ((equal n left) (mv :budget start (+ pos n) overflow))
                               (t (mv :need-more start nfill overflow)))))))))))))

(defconst *fn2-gram-frame-statuses* '(:line :long-line :overflow :need-more :budget :fault))

; ------------------------------------------------------------------------
; A complete command line [s, e): the LF is at e-1. Malformed (the line is
; refused and the connection closes after the reply, RFC 3977 sections 3.1
; and 12.5): an empty line, a bare LF, a bare CR, a NUL or ill-formed UTF-8.
; Syntax (501, the connection stays): any other control octet.
(defun fn2-gram-utf8-step (b need lo hi)
  (declare (xargs :guard (and (natp b) (natp need) (natp lo) (natp hi))))
  ; Returns (mv bad need lo hi); RFC 3629 section 4's well-formed sequences.
  (cond ((> need 0) (if (and (<= lo b) (<= b hi)) (mv nil (- need 1) #x80 #xbf) (mv t 0 #x80 #xbf)))
        ((< b #x80) (mv nil 0 #x80 #xbf))
        ((and (<= #xc2 b) (<= b #xdf)) (mv nil 1 #x80 #xbf))
        ((= b #xe0) (mv nil 2 #xa0 #xbf))
        ((or (and (<= #xe1 b) (<= b #xec)) (= b #xee) (= b #xef)) (mv nil 2 #x80 #xbf))
        ((= b #xed) (mv nil 2 #x80 #x9f))
        ((= b #xf0) (mv nil 3 #x90 #xbf))
        ((and (<= #xf1 b) (<= b #xf3)) (mv nil 3 #x80 #xbf))
        ((= b #xf4) (mv nil 3 #x80 #x8f))
        (t (mv t 0 #x80 #xbf))))

(defun fn2-gram-line-scan (left i need lo hi bad ctl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i)
                              (natp need) (natp lo) (natp hi))))
  (if (zp left) (mv bad ctl need)
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (if (not ok) (mv t ctl need)
        (mv-let (ubad need lo hi) (fn2-gram-utf8-step b need lo hi)
          (fn2-gram-line-scan (- left 1) (+ 1 i) need lo hi
                              (or bad ubad (= b 0) (= b *fn2-gram-cr*) (= b *fn2-gram-lf*))
                              (or ctl (and (< b 32) (not (= b *fn2-gram-tab*))) (= b 127))
                              slot gen okind oslot ogen fn2-pool))))))

(defun fn2-gram-wspp (b)
  (declare (xargs :guard t))
  (or (equal b *fn2-gram-sp*) (equal b *fn2-gram-tab*)))

(defun fn2-gram-check-line (s e slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp s) (natp e))))
  (if (< (- e s) 3) :malformed
    (mv-let (ok cr) (fn2-gram-read slot gen (- e 2) okind oslot ogen fn2-pool)
      (if (not (and ok (= cr *fn2-gram-cr*))) :malformed
        (mv-let (bad ctl need)
          (fn2-gram-line-scan (- (- e 2) s) s 0 #x80 #xbf nil nil slot gen okind oslot ogen fn2-pool)
          (cond ((or bad (not (equal need 0))) :malformed)
                (ctl :syntax)
                (t (mv-let (ok1 first) (fn2-gram-read slot gen s okind oslot ogen fn2-pool)
                     (mv-let (ok2 last) (fn2-gram-read slot gen (- e 3) okind oslot ogen fn2-pool)
                       (if (or (not ok1) (not ok2) (fn2-gram-wspp first) (fn2-gram-wspp last))
                           :syntax :ok))))))))))

; ------------------------------------------------------------------------
; Tokens of [i, end): runs of octets other than SP/TAB. WS non-nil skips
; whitespace, nil skips a token; returns the first index not skipped.
(defun fn2-gram-skip (left i end ws slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i) (natp end))))
  (if (or (zp left) (>= i end)) (nfix i)
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (if (or (not ok) (not (equal (fn2-gram-wspp b) (and ws t)))) (nfix i)
        (fn2-gram-skip (- left 1) (+ 1 i) end ws slot gen okind oslot ogen fn2-pool)))))
(defthm fn2-gram-skip-bounds
  (and (natp (fn2-gram-skip left i end ws slot gen okind oslot ogen fn2-pool))
       (implies (natp i) (<= i (fn2-gram-skip left i end ws slot gen okind oslot ogen fn2-pool))))
  :rule-classes ((:type-prescription :corollary
                  (natp (fn2-gram-skip left i end ws slot gen okind oslot ogen fn2-pool)))
                 (:linear :corollary
                  (implies (natp i) (<= i (fn2-gram-skip left i end ws slot gen okind oslot ogen fn2-pool))))))

; Token N (0 is the keyword) of the line [s, end): (mv found start length).
(defun fn2-gram-token (n i end slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp i) (natp end))))
  (let ((te (fn2-gram-skip (nfix (- end i)) i end nil slot gen okind oslot ogen fn2-pool)))
    (if (zp n) (mv (< i end) (nfix i) (- te (nfix i)))
      (fn2-gram-token (- n 1) (fn2-gram-skip (nfix (- end te)) te end t slot gen okind oslot ogen fn2-pool)
                      end slot gen okind oslot ogen fn2-pool))))
(defthm fn2-gram-token-natp
  (and (natp (mv-nth 1 (fn2-gram-token n i end slot gen okind oslot ogen fn2-pool)))
       (natp (mv-nth 2 (fn2-gram-token n i end slot gen okind oslot ogen fn2-pool))))
  :rule-classes ((:type-prescription :corollary (natp (mv-nth 1 (fn2-gram-token n i end slot gen okind oslot ogen fn2-pool))))
                 (:type-prescription :corollary (natp (mv-nth 2 (fn2-gram-token n i end slot gen okind oslot ogen fn2-pool))))))

; The number of tokens of [i, end), counting at most LEFT.
(defun fn2-gram-count (left i end slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i) (natp end))))
  (if (or (zp left) (>= i end)) 0
    (let* ((te (fn2-gram-skip (nfix (- end i)) i end nil slot gen okind oslot ogen fn2-pool))
           (next (fn2-gram-skip (nfix (- end te)) te end t slot gen okind oslot ogen fn2-pool)))
      (if (<= next i) 1
        (+ 1 (fn2-gram-count (- left 1) next end slot gen okind oslot ogen fn2-pool))))))

; ------------------------------------------------------------------------
; Argument validators over one token [ts, ts+tl). Each returns
; (mv ok form a b), FORM one of :number :range :span :keyword :date :time
; :gmt naming how A and B are read: a value, a (low, high) range whose open
; end is *fn2-none*, or an (offset, length) span.
(defun fn2-gram-upcase (b)
  (declare (xargs :guard (natp b)))
  (if (and (<= 97 b) (<= b 122)) (- b 32) b))

(defun fn2-gram-match-loop (k ts kw slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix (- (length kw) (nfix k)))
                  :guard (and (fn2-pool-wfp fn2-pool) (natp k) (natp ts) (stringp kw))))
  (if (or (not (stringp kw)) (>= (nfix k) (length kw))) t
    (mv-let (ok b) (fn2-gram-read slot gen (+ ts (nfix k)) okind oslot ogen fn2-pool)
      (and ok (= (fn2-gram-upcase b) (char-code (char kw (nfix k))))
           (fn2-gram-match-loop (+ 1 (nfix k)) ts kw slot gen okind oslot ogen fn2-pool)))))
; Case-insensitive equality of a token with an upper-case keyword string.
(defun fn2-gram-match (ts tl kw slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ts) (natp tl) (stringp kw))))
  (and (equal tl (length kw)) (fn2-gram-match-loop 0 ts kw slot gen okind oslot ogen fn2-pool)))

(defun fn2-gram-digits (left i acc slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i) (natp acc))))
  (if (zp left) (mv t acc)
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (if (not (and ok (<= 48 b) (<= b 57))) (mv nil 0)
        (fn2-gram-digits (- left 1) (+ 1 i) (+ (* 10 acc) (- b 48)) slot gen okind oslot ogen fn2-pool)))))
(defthm fn2-gram-digits-natp
  (implies (natp acc) (natp (mv-nth 1 (fn2-gram-digits left i acc slot gen okind oslot ogen fn2-pool))))
  :rule-classes :type-prescription)

; 1..16 decimal digits (RFC 3977 section 4.1's number), no range check.
(defun fn2-gram-arg-digits (ts tl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ts) (natp tl))))
  (if (not (and (<= 1 tl) (<= tl 16))) (mv nil :number 0 0)
    (mv-let (ok v) (fn2-gram-digits tl ts 0 slot gen okind oslot ogen fn2-pool)
      (mv ok :number v 0))))
; An article number: 1..2147483647.
(defun fn2-gram-arg-number (ts tl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ts) (natp tl))))
  (mv-let (ok form v b) (fn2-gram-arg-digits ts tl slot gen okind oslot ogen fn2-pool)
    (declare (ignore b))
    (mv (and ok (<= 1 v) (<= v *fn2-gram-article-max*)) form v 0)))

(defun fn2-gram-find (left i byte slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) (mv nil 0)
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (if (and ok (equal b byte)) (mv t (nfix i))
        (fn2-gram-find (- left 1) (+ 1 i) byte slot gen okind oslot ogen fn2-pool)))))
(defthm fn2-gram-find-natp (natp (mv-nth 1 (fn2-gram-find left i byte slot gen okind oslot ogen fn2-pool)))
  :rule-classes :type-prescription)

; n | n- | n-m (RFC 3977 section 6's range), each end an article number.
(defun fn2-gram-arg-range (ts tl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ts) (natp tl))))
  (mv-let (dash d) (fn2-gram-find tl ts *fn2-gram-dash* slot gen okind oslot ogen fn2-pool)
    (if (not dash)
        (mv-let (ok form v b) (fn2-gram-arg-number ts tl slot gen okind oslot ogen fn2-pool)
          (declare (ignore form b))
          (mv ok :range v v))
      (mv-let (ok form lo b) (fn2-gram-arg-number ts (- d ts) slot gen okind oslot ogen fn2-pool)
        (declare (ignore form b))
        (if (equal (+ 1 d) (+ ts tl)) (mv ok :range lo *fn2-none*)
          (mv-let (ok2 form2 hi b2)
            (fn2-gram-arg-number (+ 1 d) (- (+ ts tl) (+ 1 d)) slot gen okind oslot ogen fn2-pool)
            (declare (ignore form2 b2))
            (mv (and ok ok2) :range lo hi)))))))

(defun fn2-gram-msgid-middle (left i slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) t
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (and ok (or (and (<= #x21 b) (<= b #x3d)) (and (<= #x3f b) (<= b #x7e)))
           (fn2-gram-msgid-middle (- left 1) (+ 1 i) slot gen okind oslot ogen fn2-pool)))))
; A Message-ID: "<", 1..248 octets of %x21-3D / %x3F-7E, ">" (RFC 3977
; section 3.6; specs/nntp.md's 250-octet bound).
(defun fn2-gram-arg-msgid (ts tl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ts) (natp tl))))
  (if (not (and (<= 3 tl) (<= tl 250))) (mv nil :span 0 0)
    (mv-let (ok1 first) (fn2-gram-read slot gen ts okind oslot ogen fn2-pool)
      (mv-let (ok2 last) (fn2-gram-read slot gen (+ ts tl -1) okind oslot ogen fn2-pool)
        (mv (and ok1 ok2 (= first *fn2-gram-lt*) (= last *fn2-gram-gt*)
                 (fn2-gram-msgid-middle (- tl 2) (+ 1 ts) slot gen okind oslot ogen fn2-pool))
            :span ts tl)))))

; A wildmat (RFC 3977 section 4.2, as H's model checks it): alternatives
; split at ","; a "!" opens a negative alternative and never the first; no
; alternative is empty; "!", "[", "]" and "\" never occur inside one.
(defun fn2-gram-wildmat-loop (left i first atstart alen slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i) (natp alen))))
  (if (zp left) (< 0 alen)
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (cond ((not ok) nil)
            ((= b *fn2-gram-comma*)
             (and (< 0 alen) (fn2-gram-wildmat-loop (- left 1) (+ 1 i) nil t 0 slot gen okind oslot ogen fn2-pool)))
            ((and atstart (= b *fn2-gram-bang*))
             (and (not first) (fn2-gram-wildmat-loop (- left 1) (+ 1 i) first nil 0 slot gen okind oslot ogen fn2-pool)))
            ((or (= b *fn2-gram-bang*) (= b 91) (= b 93) (= b 92)) nil)
            (t (fn2-gram-wildmat-loop (- left 1) (+ 1 i) first nil (+ 1 alen) slot gen okind oslot ogen fn2-pool))))))
(defun fn2-gram-arg-wildmat (ts tl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ts) (natp tl))))
  (mv (fn2-gram-wildmat-loop tl ts t t 0 slot gen okind oslot ogen fn2-pool) :span ts tl))

; A capability label: [A-Za-z][A-Za-z0-9.-]{2,} (RFC 3977 section 3.3.1).
(defun fn2-gram-label-loop (left i slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) t
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (let ((u (fn2-gram-upcase b)))
        (and ok (or (and (<= 65 u) (<= u 90)) (and (<= 48 b) (<= b 57))
                    (= b *fn2-gram-dot*) (= b *fn2-gram-dash*))
             (fn2-gram-label-loop (- left 1) (+ 1 i) slot gen okind oslot ogen fn2-pool))))))
(defun fn2-gram-arg-label (ts tl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ts) (natp tl))))
  (mv-let (ok b) (fn2-gram-read slot gen ts okind oslot ogen fn2-pool)
    (let ((u (fn2-gram-upcase b)))
      (mv (and ok (<= 3 tl) (<= 65 u) (<= u 90)
               (fn2-gram-label-loop (- tl 1) (+ 1 ts) slot gen okind oslot ogen fn2-pool))
          :span ts tl))))

; NEWGROUPS/NEWNEWS date (6 or 8 digits) and time (6 digits), RFC 3977 7.3.
(defun fn2-gram-arg-date (ts tl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ts) (natp tl))))
  (mv-let (ok v) (fn2-gram-digits tl ts 0 slot gen okind oslot ogen fn2-pool)
    (mv (and ok (or (= tl 6) (= tl 8))) :date v tl)))
(defun fn2-gram-arg-time (ts tl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ts) (natp tl))))
  (mv-let (ok v) (fn2-gram-digits tl ts 0 slot gen okind oslot ogen fn2-pool)
    (mv (and ok (= tl 6)) :time v 0)))

; Every argument kind but (:keyword ...), which the grammar compiles into
; its own matcher. :ref and :ref-range read a Message-ID when the token
; opens with "<", else a number or a range.
(defun fn2-gram-arg (kind ts tl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ts) (natp tl))))
  (case kind
    (:number (fn2-gram-arg-number ts tl slot gen okind oslot ogen fn2-pool))
    (:digits (fn2-gram-arg-digits ts tl slot gen okind oslot ogen fn2-pool))
    (:range (fn2-gram-arg-range ts tl slot gen okind oslot ogen fn2-pool))
    (:msgid (fn2-gram-arg-msgid ts tl slot gen okind oslot ogen fn2-pool))
    ((:ref :ref-range)
     (mv-let (ok b) (fn2-gram-read slot gen ts okind oslot ogen fn2-pool)
       (if (and ok (= b *fn2-gram-lt*)) (fn2-gram-arg-msgid ts tl slot gen okind oslot ogen fn2-pool)
         (if (eq kind :ref) (fn2-gram-arg-number ts tl slot gen okind oslot ogen fn2-pool)
           (fn2-gram-arg-range ts tl slot gen okind oslot ogen fn2-pool)))))
    (:wildmat (fn2-gram-arg-wildmat ts tl slot gen okind oslot ogen fn2-pool))
    (:label (fn2-gram-arg-label ts tl slot gen okind oslot ogen fn2-pool))
    (:date (fn2-gram-arg-date ts tl slot gen okind oslot ogen fn2-pool))
    (:time (fn2-gram-arg-time ts tl slot gen okind oslot ogen fn2-pool))
    (:gmt (mv (fn2-gram-match ts tl "GMT" slot gen okind oslot ogen fn2-pool) :gmt 1 0))
    (otherwise (mv t :span ts tl))))

(defconst *fn2-gram-arg-kinds*
  '(:number :digits :range :msgid :ref :ref-range :wildmat :label :date :time :gmt :token :rest :keyword))

; ------------------------------------------------------------------------
; Multi-line blocks (article input, RFC 3977 section 3.1.1). One call
; frames one block line: :data [ds, de) after dot-unstuffing, :terminator
; for ".CRLF", :bad-line for a bare LF, a NUL or bare CR, or an unescaped
; leading dot (the block is refused and discarded to its terminator), or
; the framer's own statuses. The caller discards to the terminator after a
; refusal by ignoring :data.
(defun fn2-gram-block-scan (left i slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) t
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (and ok (not (= b 0)) (not (= b *fn2-gram-cr*))
           (fn2-gram-block-scan (- left 1) (+ 1 i) slot gen okind oslot ogen fn2-pool)))))

(defun fn2-gram-block-step (left start pos overflow cap slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp start) (natp pos)
                              (<= start pos) (bitp overflow) (posp cap))))
  (mv-let (status s p o) (fn2-gram-frame left start pos overflow cap slot gen okind oslot ogen fn2-pool)
    (if (not (eq status :line)) (mv status s p o 0 0)
      (mv-let (ok cr) (fn2-gram-read slot gen (- p 2) okind oslot ogen fn2-pool)
        (if (not (and ok (<= 2 (- p s)) (= cr *fn2-gram-cr*))) (mv :bad-line s p o 0 0)
          (mv-let (ok1 first) (fn2-gram-read slot gen s okind oslot ogen fn2-pool)
            (mv-let (ok2 second) (fn2-gram-read slot gen (+ 1 s) okind oslot ogen fn2-pool)
              (cond ((not (fn2-gram-block-scan (- (- p 2) s) s slot gen okind oslot ogen fn2-pool))
                     (mv :bad-line s p o 0 0))
                    ((and ok1 (= first *fn2-gram-dot*) (= (- p s) 3)) (mv :terminator s p o 0 0))
                    ((and ok1 (= first *fn2-gram-dot*))
                     (if (and ok2 (= second *fn2-gram-dot*)) (mv :data s p o (+ 1 s) (- p 2))
                       (mv :bad-line s p o 0 0)))
                    (t (mv :data s p o s (- p 2)))))))))))

; A line framed structurally: [s, e) ends in CRLF and holds no other NUL,
; CR or LF (its UTF-8 and its control octets may still be refused). A
; refused command whose block follows at once is told apart by this.
(defun fn2-gram-clean-scan (left i slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) t
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (and ok (not (= b 0)) (not (= b *fn2-gram-cr*)) (not (= b *fn2-gram-lf*))
           (fn2-gram-clean-scan (- left 1) (+ 1 i) slot gen okind oslot ogen fn2-pool)))))
(defun fn2-gram-structural-p (s e slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp s) (natp e))))
  (and (<= (+ s 3) e)
       (mv-let (ok cr) (fn2-gram-read slot gen (- e 2) okind oslot ogen fn2-pool)
         (and ok (= cr *fn2-gram-cr*)))
       (fn2-gram-clean-scan (- (- e 2) s) s slot gen okind oslot ogen fn2-pool)))

; ------------------------------------------------------------------------
; Rendering into a TX slot, appended at its fill through fn2-pool-write.
(defun fn2-gram-put (byte slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp byte))))
  (fn2-pool-write slot gen (fn2-gram-fill slot fn2-pool) byte okind oslot ogen fn2-pool))
(fn2-pool-preserves fn2-gram-put (byte slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)

(defun fn2-gram-pow10 (left n p)
  (declare (xargs :guard (and (natp left) (natp n) (posp p)) :measure (nfix left)))
  (if (or (zp left) (< n (* 10 p))) p (fn2-gram-pow10 (- left 1) n (* 10 p))))
(defthm fn2-gram-pow10-posp (implies (posp p) (posp (fn2-gram-pow10 left n p))) :rule-classes :type-prescription)

; N in decimal, digits from the power P down (P a power of ten).
(defun fn2-gram-digit-byte (n p)
  (declare (xargs :guard (and (natp n) (posp p))))
  (+ 48 (nfix (mod (floor n p) 10))))
(defthm fn2-gram-digit-byte-natp (natp (fn2-gram-digit-byte n p)) :rule-classes :type-prescription)
(defun fn2-gram-next-power (p)
  (declare (xargs :guard (natp p)))
  (nfix (floor p 10)))
(defthm fn2-gram-next-power-natp (natp (fn2-gram-next-power p)) :rule-classes :type-prescription)
(in-theory (disable fn2-gram-digit-byte fn2-gram-next-power))
(defun fn2-gram-put-digits (left n p slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp n) (natp p))))
  (if (or (zp left) (zp p)) (mv :ok fn2-pool)
    (mv-let (code fn2-pool) (fn2-gram-put (fn2-gram-digit-byte n p) slot gen okind oslot ogen fn2-pool)
      (if (not (eq code :ok)) (mv code fn2-pool)
        (fn2-gram-put-digits (- left 1) n (fn2-gram-next-power p) slot gen okind oslot ogen fn2-pool)))))
(fn2-pool-preserves fn2-gram-put-digits (left n p slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
(defun fn2-gram-put-number (n slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp n))))
  (fn2-gram-put-digits 20 n (fn2-gram-pow10 20 n 1) slot gen okind oslot ogen fn2-pool))
(fn2-pool-preserves fn2-gram-put-number (n slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
(defun fn2-gram-put-digits14 (n slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp n))))
  (fn2-gram-put-digits 14 n 10000000000000 slot gen okind oslot ogen fn2-pool))
(fn2-pool-preserves fn2-gram-put-digits14 (n slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)

; Copy [i, i+left) of a source slot of the same owner.
(defun fn2-gram-put-span (left i sslot sgen slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) (mv :ok fn2-pool)
    (mv-let (ok b) (fn2-gram-read sslot sgen i okind oslot ogen fn2-pool)
      (if (not ok) (mv :span fn2-pool)
        (mv-let (code fn2-pool) (fn2-gram-put b slot gen okind oslot ogen fn2-pool)
          (if (not (eq code :ok)) (mv code fn2-pool)
            (fn2-gram-put-span (- left 1) (+ 1 i) sslot sgen slot gen okind oslot ogen fn2-pool)))))))
(fn2-pool-preserves fn2-gram-put-span (left i sslot sgen slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)

; A compiled template: literal octets, and field markers taking N0, N1, N2
; in order (numbers) or the one span. K is the next template position.
(defun fn2-gram-put-template (k tmpl nidx n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix (- (length tmpl) (nfix k)))
                  :guard (and (fn2-pool-wfp fn2-pool) (natp k) (stringp tmpl) (natp nidx)
                              (natp n0) (natp n1) (natp n2) (natp soff) (natp slen))))
  (if (or (not (stringp tmpl)) (>= (nfix k) (length tmpl))) (mv :ok fn2-pool)
    (let* ((c (char-code (char tmpl (nfix k))))
           (n (cond ((equal nidx 0) n0) ((equal nidx 1) n1) (t n2))))
      (mv-let (code fn2-pool)
        (cond ((= c *fn2-gram-field-number*) (fn2-gram-put-number n slot gen okind oslot ogen fn2-pool))
              ((= c *fn2-gram-field-digits14*) (fn2-gram-put-digits14 n slot gen okind oslot ogen fn2-pool))
              ((= c *fn2-gram-field-span*)
               (fn2-gram-put-span slen soff sslot sgen slot gen okind oslot ogen fn2-pool))
              (t (fn2-gram-put c slot gen okind oslot ogen fn2-pool)))
        (if (not (eq code :ok)) (mv code fn2-pool)
          (fn2-gram-put-template (+ 1 (nfix k)) tmpl
            (if (or (= c *fn2-gram-field-number*) (= c *fn2-gram-field-digits14*)) (+ 1 nidx) nidx)
            n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen fn2-pool))))))
(fn2-pool-preserves fn2-gram-put-template (k tmpl nidx n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)

(defun fn2-gram-put-crlf (slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (mv-let (code fn2-pool) (fn2-gram-put *fn2-gram-cr* slot gen okind oslot ogen fn2-pool)
    (if (not (eq code :ok)) (mv code fn2-pool)
      (fn2-gram-put *fn2-gram-lf* slot gen okind oslot ogen fn2-pool))))
(fn2-pool-preserves fn2-gram-put-crlf (slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)

; One dot-stuffed block line from a source span, and the terminator.
(defun fn2-gram-put-block-line (sslot sgen soff slen slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp soff) (natp slen))))
  (mv-let (ok first) (fn2-gram-read sslot sgen soff okind oslot ogen fn2-pool)
    (mv-let (code fn2-pool)
      (if (and ok (< 0 slen) (= first *fn2-gram-dot*))
          (fn2-gram-put *fn2-gram-dot* slot gen okind oslot ogen fn2-pool)
        (mv :ok fn2-pool))
      (if (not (eq code :ok)) (mv code fn2-pool)
        (mv-let (code fn2-pool) (fn2-gram-put-span slen soff sslot sgen slot gen okind oslot ogen fn2-pool)
          (if (not (eq code :ok)) (mv code fn2-pool)
            (fn2-gram-put-crlf slot gen okind oslot ogen fn2-pool)))))))
(fn2-pool-preserves fn2-gram-put-block-line (sslot sgen soff slen slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
(defun fn2-gram-put-terminator (slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (mv-let (code fn2-pool) (fn2-gram-put *fn2-gram-dot* slot gen okind oslot ogen fn2-pool)
    (if (not (eq code :ok)) (mv code fn2-pool)
      (fn2-gram-put-crlf slot gen okind oslot ogen fn2-pool))))
(fn2-pool-preserves fn2-gram-put-terminator (slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)

; ------------------------------------------------------------------------
; The five generic obligations' framer halves (the per-grammar halves are
; emitted by DEFGRAMMAR). Hypotheses are the guard only: no premise on the
; octets.
(defun fn2-gram-frame-shape-p (left start pos cap status start2 pos2 overflow2 nfill)
  (declare (xargs :guard t))
  (and (member-eq status *fn2-gram-frame-statuses*)
       (natp start2) (natp pos2) (bitp overflow2) (<= start2 pos2)
       ; Linear consumption: never backwards, at most LEFT octets, never past fill.
       (natp pos) (<= pos pos2) (<= pos2 (+ pos (nfix left)))
       (or (equal pos2 pos) (<= pos2 (nfix nfill)))
       ; Bounded retention: a retained partial line never exceeds the cap.
       (natp cap) (<= (- pos2 start2) cap)
       (or (not (equal status :line)) (and (< start2 pos2) (natp start) (<= start start2)))))

(defun fn2-gram-frame-outcome-p (left start pos overflow cap slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp start) (natp pos)
                              (<= start pos) (bitp overflow) (posp cap))))
  (mv-let (status start2 pos2 overflow2)
    (fn2-gram-frame left start pos overflow cap slot gen okind oslot ogen fn2-pool)
    (fn2-gram-frame-shape-p left start pos cap status start2 pos2 overflow2
                            (fn2-gram-fill slot fn2-pool))))

(defthm-owed fn2-gram-frame-total-linear (left start pos overflow cap slot gen okind oslot ogen pool)
  (implies (and (fn2-poolp pool) (fn2-pool-wfp pool) (natp left) (natp start) (natp pos)
                (<= start pos) (<= (- pos start) cap) (bitp overflow) (posp cap))
           (fn2-gram-frame-outcome-p left start pos overflow cap slot gen okind oslot ogen pool))
  :schema :bound :from (:operation-set fn2-grammar)
  :teeth (fn2-gram-test-frame-shapes fn2-gram-test-frame-shapes-negative)
  :doc "Over arbitrary octets, the framer returns a declared status, never moves backwards, consumes at most its budget and never past fill, and retains at most the line cap (totality, linear consumption, bounded retention).")

; ========================================================================
; DEFGRAMMAR. The declaration:
;   (defgrammar NAME
;     :line-cap N :args-cap N :block-line-cap N
;     :states (S ...)                     ; protocol state bits, in order
;     :layers ((LAYER STATE-or-nil) ...)  ; a reply's layer and the state it needs
;     :fields ((WORD :number|:span|:digits14) ...)   ; template field words
;     :general ((KEY :code N :text T :layer L :class C) ...)   ; replies of no command
;     :commands ((CMD :keyword K :args (ARG ...) :states (S ...) :state-refusal KEY
;                     :block nil|(:after CODE)|(:immediate) :block-refusal KEY
;                     :hand-off nil|(:tls CODE)|(:compress CODE)
;                     :help ROW-or-nil :spec "citation"
;                     :replies ((KEY :code N :text T :layer L :class C) ...)) ...))
; An ARG is a kind of *fn2-gram-arg-kinds* but :keyword, (:keyword W ...),
; or (:opt ARG); :rest takes the line from its token and must be last.
; An (:immediate) block follows its command line without waiting for a
; reply (TAKETHIS, RFC 4644 section 2.5): a refused line of such a command
; whose keyword stands first, in a state that admits it and with structural
; framing, parses to :discard; its block is framed and discarded, and its
; :block-refusal reply is due after the terminator.
; Expansion helpers run at macro time only (lists live there, never at run time).

(defun fn2-gram-cat (parts)
  (declare (xargs :verify-guards nil))
  (if (atom parts) ""
    (concatenate 'string
                 (let ((p (car parts)))
                   (cond ((stringp p) p) ((symbolp p) (symbol-name p))
                         ((natp p) (coerce (explode-nonnegative-integer p 10 nil) 'string)) (t "")))
                 (fn2-gram-cat (cdr parts)))))
(defun fn2-gram-symbol (parts)
  (declare (xargs :verify-guards nil))
  (intern-in-package-of-symbol (string-upcase (fn2-gram-cat parts)) 'fn2-gram-symbol))
(defmacro fn2-gram-sym (&rest parts) `(fn2-gram-symbol (list ,@parts)))
(defmacro fn2-gram-const (&rest parts) `(fn2-gram-symbol (list "*" ,@parts "*")))

(defun fn2-gram-arg-opt-p (arg) (declare (xargs :verify-guards nil)) (and (consp arg) (eq (car arg) :opt)))
(defun fn2-gram-arg-base (arg) (declare (xargs :verify-guards nil)) (if (fn2-gram-arg-opt-p arg) (cadr arg) arg))
(defun fn2-gram-args-required (args)
  (declare (xargs :verify-guards nil))
  (if (atom args) 0 (if (fn2-gram-arg-opt-p (car args)) 0 (+ 1 (fn2-gram-args-required (cdr args))))))
(defun fn2-gram-args-rest-p (args)
  (declare (xargs :verify-guards nil))
  (and (consp args) (or (eq (fn2-gram-arg-base (car args)) :rest) (fn2-gram-args-rest-p (cdr args)))))
(defun fn2-gram-argp (arg)
  (declare (xargs :verify-guards nil))
  (let ((b (fn2-gram-arg-base arg)))
    (or (and (keywordp b) (member-eq b *fn2-gram-arg-kinds*) (not (eq b :keyword)))
        (and (consp b) (eq (car b) :keyword) (consp (cdr b)) (string-listp (cdr b))))))
(defun fn2-gram-args-p (args)
  (declare (xargs :verify-guards nil))
  (if (atom args) (null args)
    (and (fn2-gram-argp (car args)) (<= (len args) 4)
         (or (not (eq (fn2-gram-arg-base (car args)) :rest)) (null (cdr args)))
         (or (fn2-gram-arg-opt-p (car args))
             (fn2-gram-args-required (list (car args))))
         (fn2-gram-args-p (cdr args)))))

(defun fn2-gram-reply-p (reply)
  (declare (xargs :verify-guards nil))
  (and (consp reply) (keywordp (car reply)) (keyword-value-listp (cdr reply))
       (natp (fn2-decl-get :code (cdr reply))) (<= 100 (fn2-decl-get :code (cdr reply)))
       (< (fn2-decl-get :code (cdr reply)) 600)
       (stringp (fn2-decl-get :text (cdr reply)))
       ; The text opens with its own code: the rendered status is the declared one.
       (<= 4 (length (fn2-decl-get :text (cdr reply))))
       (equal (subseq (fn2-decl-get :text (cdr reply)) 0 3)
              (coerce (explode-nonnegative-integer (fn2-decl-get :code (cdr reply)) 10 nil) 'string))
       (keywordp (fn2-decl-get :layer (cdr reply)))
       (member-eq (fn2-decl-get :class (cdr reply)) '(:accepted :refused :uncertain))))
(defun fn2-gram-replies-p (replies)
  (declare (xargs :verify-guards nil))
  (if (atom replies) (null replies)
    (and (fn2-gram-reply-p (car replies)) (not (assoc-eq (caar replies) (cdr replies)))
         (fn2-gram-replies-p (cdr replies)))))

; Template compilation: a word of the text that is a declared field word
; becomes its marker character; every other octet is literal.
(defun fn2-gram-split-words (chars word acc)
  (declare (xargs :verify-guards nil))
  (cond ((atom chars) (reverse (cons (coerce (reverse word) 'string) acc)))
        ((eql (car chars) #\Space) (fn2-gram-split-words (cdr chars) nil (cons (coerce (reverse word) 'string) acc)))
        (t (fn2-gram-split-words (cdr chars) (cons (car chars) word) acc))))
(defun fn2-gram-field-marker (kind)
  (declare (xargs :verify-guards nil))
  (code-char (case kind (:number *fn2-gram-field-number*) (:span *fn2-gram-field-span*)
               (otherwise *fn2-gram-field-digits14*))))
(defun fn2-gram-compile-words (words fields)
  (declare (xargs :verify-guards nil))
  (if (atom words) ""
    (let* ((f (assoc-equal (car words) fields))
           (w (if f (coerce (list (fn2-gram-field-marker (cadr f))) 'string) (car words))))
      (if (atom (cdr words)) w (concatenate 'string w " " (fn2-gram-compile-words (cdr words) fields))))))
(defun fn2-gram-template (text fields)
  (declare (xargs :verify-guards nil))
  (fn2-gram-compile-words (fn2-gram-split-words (coerce text 'list) nil nil) fields))

; Flatten (command-tag reply) pairs: general replies belong to the none tag.
(defun fn2-gram-reply-rows (cmd-name tag replies)
  (declare (xargs :verify-guards nil))
  (if (atom replies) nil
    (cons (list* cmd-name tag (car replies)) (fn2-gram-reply-rows cmd-name tag (cdr replies)))))
(defun fn2-gram-all-reply-rows (commands tag)
  (declare (xargs :verify-guards nil))
  (if (atom commands) nil
    (append (fn2-gram-reply-rows (caar commands) tag (fn2-decl-get :replies (cdar commands)))
            (fn2-gram-all-reply-rows (cdr commands) (+ 1 tag)))))

(defun fn2-gram-state-mask (states declared)
  (declare (xargs :verify-guards nil))
  (if (atom states) 0
    (logior (expt 2 (nfix (position-eq (car states) declared)))
            (fn2-gram-state-mask (cdr states) declared))))

(defun fn2-gram-reply-name (g row)
  (declare (xargs :verify-guards nil))
  ; row = (cmd-name tag key . plist)
  (if (car row) (fn2-gram-const g "-reply-" (car row) "-" (caddr row)) (fn2-gram-const g "-reply-" (caddr row))))

(defun fn2-gram-reply-consts (g rows index)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (cons `(defconst ,(fn2-gram-reply-name g (car rows)) ,index)
          (fn2-gram-reply-consts g (cdr rows) (+ 1 index)))))
(defun fn2-gram-reply-arms (rows index key fields)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let* ((row (car rows)) (plist (cdddr row)))
      (cons (list index
                  (case key
                    (:command (cadr row))
                    (:code (fn2-decl-get :code plist))
                    (:template (fn2-gram-template (fn2-decl-get :text plist) fields))
                    (:layer (list 'quote (fn2-decl-get :layer plist)))
                    (otherwise (list 'quote (fn2-decl-get :class plist)))))
            (fn2-gram-reply-arms (cdr rows) (+ 1 index) key fields)))))

(defun fn2-gram-command-consts (g commands tag)
  (declare (xargs :verify-guards nil))
  (if (atom commands) nil
    (cons `(defconst ,(fn2-gram-const g "-command-" (caar commands)) ,tag)
          (fn2-gram-command-consts g (cdr commands) (+ 1 tag)))))
(defun fn2-gram-keyword-arms (g commands)
  (declare (xargs :verify-guards nil))
  (if (atom commands) nil
    (cons `((fn2-gram-match ts tl ,(fn2-decl-get :keyword (cdar commands)) slot gen okind oslot ogen fn2-pool)
            ,(fn2-gram-const g "-command-" (caar commands)))
          (fn2-gram-keyword-arms g (cdr commands)))))
(defun fn2-gram-command-arms (g commands tag key declared)
  (declare (xargs :verify-guards nil))
  (if (atom commands) nil
    (let ((p (cdar commands)))
      (cons (list tag
                  (case key
                    (:states (fn2-gram-state-mask (fn2-decl-get :states p) declared))
                    (:refusal (let ((r (fn2-decl-get :state-refusal p)))
                                (if r (fn2-gram-const g "-reply-" (caar commands) "-" r) (fn2-gram-const g "-reply-none"))))
                    (:block-refusal (let ((r (fn2-decl-get :block-refusal p)))
                                      (if r (fn2-gram-const g "-reply-" (caar commands) "-" r) (fn2-gram-const g "-reply-none"))))
                    (:block (list 'quote (car (fn2-decl-get :block p))))
                    (:block-code (or (cadr (fn2-decl-get :block p)) 0))
                    (:hand-off (list 'quote (car (fn2-decl-get :hand-off p))))
                    (:hand-off-code (or (cadr (fn2-decl-get :hand-off p)) 0))
                    (otherwise `(,(fn2-gram-sym g "-args-" (caar commands)) s end slot gen okind oslot ogen fn2-pool))))
            (fn2-gram-command-arms g (cdr commands) (+ 1 tag) key declared)))))

; One argument's validation, as a form returning (mv ok form a b).
(defun fn2-gram-keyword-match-arms (words index)
  (declare (xargs :verify-guards nil))
  (if (atom words) '((t (mv nil :keyword 0 0)))
    (cons `((fn2-gram-match ts tl ,(car words) slot gen okind oslot ogen fn2-pool) (mv t :keyword ,index 0))
          (fn2-gram-keyword-match-arms (cdr words) (+ 1 index)))))
(defun fn2-gram-arg-form (kind)
  (declare (xargs :verify-guards nil))
  (cond ((consp kind) `(cond ,@(fn2-gram-keyword-match-arms (cdr kind) 0)))
        ((eq kind :rest) '(mv t :span ts (nfix (- end ts))))
        (t `(fn2-gram-arg ,kind ts tl slot gen okind oslot ogen fn2-pool))))
(defun fn2-gram-arg-bindings (args i)
  (declare (xargs :verify-guards nil))
  (if (atom args) nil
    (let ((ok (fn2-gram-sym "ok" i)) (f (fn2-gram-sym "f" i)) (a (fn2-gram-sym "a" i)) (b (fn2-gram-sym "b" i)))
      (append
       `(((mv ,ok ,f ,a ,b)
          (if (< ,i nargs)
              (mv-let (found ts tl) (fn2-gram-token ,(+ i 1) s end slot gen okind oslot ogen fn2-pool)
                (declare (ignorable ts tl))
                (if (not found) (mv nil :absent 0 0) ,(fn2-gram-arg-form (fn2-gram-arg-base (car args)))))
            (mv t :absent 0 0)))
         ((unless ,ok) (mv :syntax 0 :absent 0 0 :absent 0 0 :absent 0 0 :absent 0 0)))
       (fn2-gram-arg-bindings (cdr args) (+ 1 i))))))
(defun fn2-gram-arg-results (n i)
  (declare (xargs :verify-guards nil :measure (nfix (- 4 (nfix i)))))
  (if (>= (nfix i) 4) nil
    (append (if (< i n) (list (fn2-gram-sym "f" i) (fn2-gram-sym "a" i) (fn2-gram-sym "b" i)) '(:absent 0 0))
            (fn2-gram-arg-results n (+ 1 (nfix i))))))
(defun fn2-gram-args-defun (g cmd args)
  (declare (xargs :verify-guards nil))
  (let ((req (fn2-gram-args-required args)) (max (len args)) (rest (fn2-gram-args-rest-p args)))
    `(defun ,(fn2-gram-sym g "-args-" cmd) (s end slot gen okind oslot ogen fn2-pool)
       (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp s) (natp end))))
       (let ((nargs (nfix (- (fn2-gram-count 6 s end slot gen okind oslot ogen fn2-pool) 1))))
         (if (not (and (<= ,req nargs) ,(if rest t `(<= nargs ,max))))
             (mv :syntax 0 :absent 0 0 :absent 0 0 :absent 0 0 :absent 0 0)
           (b* (,@(fn2-gram-arg-bindings args 0))
             (mv :ok ,(if rest (len args) 'nargs) ,@(fn2-gram-arg-results (len args) 0))))))))

(defun fn2-gram-help-rows (commands row)
  (declare (xargs :verify-guards nil))
  (if (atom commands) nil
    (append (and (equal (fn2-decl-get :help (cdar commands)) row) (list (fn2-decl-get :keyword (cdar commands))))
            (fn2-gram-help-rows (cdr commands) row))))
(defun fn2-gram-join (words sep)
  (declare (xargs :verify-guards nil))
  (if (atom words) "" (if (atom (cdr words)) (car words) (concatenate 'string (car words) sep (fn2-gram-join (cdr words) sep)))))
(defun fn2-gram-help-text (commands row)
  (declare (xargs :verify-guards nil :measure (nfix (- 16 (nfix row)))))
  (let ((words (fn2-gram-help-rows commands row)))
    (if (or (atom words) (>= (nfix row) 16)) ""
      (concatenate 'string (fn2-gram-join words " ") (coerce (list (code-char 13) (code-char 10)) 'string)
                   (fn2-gram-help-text commands (+ 1 (nfix row)))))))

(defun fn2-gram-layer-arms (layers declared)
  (declare (xargs :verify-guards nil))
  (if (atom layers) nil
    (cons (list (caar layers) (if (cadar layers) (fn2-gram-state-mask (list (cadar layers)) declared) -1))
          (fn2-gram-layer-arms (cdr layers) declared))))

(defun fn2-gram-declarations (g commands)
  (declare (xargs :verify-guards nil))
  (if (atom commands) nil
    (let ((p (cdar commands)))
      (cons (fn2-declare (list :command (fn2-gram-sym g "-" (caar commands)))
              (list :grammar g :keyword (fn2-decl-get :keyword p) :syntax (fn2-decl-get :args p)
                    :protocol-states (fn2-decl-get :states p) :state-refusal (fn2-decl-get :state-refusal p)
                    :block (fn2-decl-get :block p) :block-refusal (fn2-decl-get :block-refusal p)
                    :hand-off (fn2-decl-get :hand-off p)
                    :help (fn2-decl-get :help p) :spec (fn2-decl-get :spec p)
                    :replies (fn2-decl-get :replies p))
              nil
              (list (fn2-gram-args-defun g (caar commands) (fn2-decl-get :args p))))
            (fn2-gram-declarations g (cdr commands))))))

(defun fn2-gram-commands-p (commands states)
  (declare (xargs :verify-guards nil))
  (if (atom commands) (null commands)
    (let ((p (cdar commands)))
      (and (symbolp (caar commands)) (keyword-value-listp p)
           (stringp (fn2-decl-get :keyword p))
           (equal (fn2-decl-get :keyword p) (string-upcase (fn2-decl-get :keyword p)))
           (fn2-gram-args-p (fn2-decl-get :args p))
           (consp (fn2-decl-get :states p)) (subsetp-eq (fn2-decl-get :states p) states)
           (stringp (fn2-decl-get :spec p))
           (fn2-gram-replies-p (fn2-decl-get :replies p))
           (or (null (fn2-decl-get :state-refusal p))
               (assoc-eq (fn2-decl-get :state-refusal p) (fn2-decl-get :replies p)))
           ; An immediate block names the reply that refuses it after the terminator.
           (iff (equal (fn2-decl-get :block p) '(:immediate)) (fn2-decl-get :block-refusal p))
           (or (null (fn2-decl-get :block-refusal p))
               (assoc-eq (fn2-decl-get :block-refusal p) (fn2-decl-get :replies p)))
           (not (assoc-eq (caar commands) (cdr commands)))
           (fn2-gram-commands-p (cdr commands) states)))))

;; A parse outcome's shape: a declared code, a tag within the enum (the none
;; tag only for refusals before a keyword is known), at most four arguments.
(defun fn2-gram-parse-shape-p (code tag nargs none)
  (declare (xargs :guard t))
  (and (member-eq code '(:ok :malformed :syntax :unknown :state :discard))
       (natp tag) (natp none) (<= tag none) (natp nargs) (<= nargs 4)
       (or (not (member-eq code '(:ok :state :discard))) (< tag none))
       (or (not (eq code :unknown)) (equal tag none))))

(defun fn2-gram-octetsp (x)
  (declare (xargs :guard t))
  (if (atom x) (null x) (and (natp (car x)) (< (car x) 256) (fn2-gram-octetsp (cdr x)))))

;; Mutation controls (D2b, RELEASE-PLAN section 2.4): the logical runner
;; takes FAULT, which is nil in every statement and every served use. Each
;; named fault makes the runner a deliberately wrong grammar that the fuzzer
;; (tests/grammar-fuzz.lisp) must catch: :accept takes an argument the
;; command's syntax refuses (a wrong acceptance), :reply answers a syntax
;; refusal with the unknown-command reply (a wrong reply), :drop keeps the
;; connection open after a malformed line (a dropped effect: the close).
(defconst *fn2-gram-faults* '(:accept :reply :drop))
(defun fn2-gram-fault-code (fault code tag none)
  (declare (xargs :guard t))
  (if (and (eq fault :accept) (eq code :syntax) (natp tag) (natp none) (< tag none)) :ok code))
(defun fn2-gram-fault-reply (fault reply rsyntax runknown)
  (declare (xargs :guard t))
  (if (and (eq fault :reply) (equal reply rsyntax)) runknown reply))

;; The first reply row of each command tag, by index.
(defun fn2-gram-first-reply-arms (rows index last)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (if (equal (cadar rows) last) (fn2-gram-first-reply-arms (cdr rows) (+ 1 index) last)
      (cons (list (cadar rows) index) (fn2-gram-first-reply-arms (cdr rows) (+ 1 index) (cadar rows))))))

;; The grammar's logical views and owed obligations. The transcript runner is
;; the fragmentation statement's subject: it is a test/logic view over an
;; octet list (lists are fine here; no served path calls it), driving the
;; real framer, parser and renderer over a local pool whose RX slot receives
;; the octets in the given chunk sizes. It assumes every block-opening reply
;; is granted and stops at a malformed line, an overflow or a hand-off.
(defun fn2-gram-logical-events (g)
  (declare (xargs :verify-guards nil))
  (let* ((none (fn2-gram-const g "-command-none"))
         (cap (fn2-gram-const g "-line-cap"))
         (bcap (fn2-gram-const g "-block-line-cap"))
         (parse (fn2-gram-sym g "-parse-line"))
         (render (fn2-gram-sym g "-render"))
         (rsyntax (fn2-gram-const g "-reply-syntax"))
         (runknown (fn2-gram-const g "-reply-unknown"))
         (respond (fn2-gram-sym g "-respond"))
         (drive (fn2-gram-sym g "-drive"))
         (run (fn2-gram-sym g "-run"))
         (run-fault (fn2-gram-sym g "-run-fault")))
    `((defun ,(fn2-gram-sym g "-parse-outcome-p") (s e mask slot gen okind oslot ogen fn2-pool)
        (declare (xargs :stobjs fn2-pool :verify-guards nil))
        (mv-let (code tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3)
          (,parse s e mask slot gen okind oslot ogen fn2-pool)
          (declare (ignore f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3))
          (fn2-gram-parse-shape-p code tag nargs ,none)))
      (defun-nx ,(fn2-gram-sym g "-render-typed-p") (cmd reply mask n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen pool)
        (let ((code (mv-nth 0 (,render cmd reply mask n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen pool))))
          (or (not (eq code :ok))
              (and (equal (,(fn2-gram-sym g "-reply-command") reply) cmd)
                   (,(fn2-gram-sym g "-reply-admitted") reply mask)))))
      ;; The reply a test responder gives a parse outcome: the command's first
      ;; reply when it parsed, else the typed refusal.
      (defun ,respond (code tag)
        (declare (xargs :guard t))
        (case code
          (:ok (mv tag (,(fn2-gram-sym g "-first-reply") tag)))
          (:unknown (mv ,none ,runknown))
          (:state (mv tag (,(fn2-gram-sym g "-state-refusal") tag)))
          (otherwise (mv ,none ,rsyntax))))
      (defun ,drive (fuel mode start pos overflow mask fault events slot gen tslot tgen fn2-pool)
        (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix fuel)))
        (if (or (zp fuel) (eq mode :stopped)) (mv mode start pos overflow events fn2-pool)
          (if (or (eq mode :block) (consp mode))
              (mv-let (status s p o ds de)
                (fn2-gram-block-step *fn2-gram-run-bytes* start pos overflow ,bcap slot gen 1 1 1 fn2-pool)
                (case status
                  ((:need-more) (mv mode s p o events fn2-pool))
                  ((:budget) (,drive (- fuel 1) mode s p o mask fault events slot gen tslot tgen fn2-pool))
                  ((:fault) (mv :stopped s p o (cons (list :fault) events) fn2-pool))
                  ((:overflow) (,drive (- fuel 1) mode s p o mask fault (cons (list :block-overflow) events) slot gen tslot tgen fn2-pool))
                  (otherwise
                   (if (and (eq status :terminator) (consp mode))
                       ;; A discarded block's refusal, due after its terminator.
                       (mv-let (rcode fn2-pool)
                         (,render (cadr mode) (,(fn2-gram-sym g "-block-refusal") (cadr mode))
                                  mask 0 0 0 slot gen s 0 tslot tgen 1 1 1 fn2-pool)
                         (,drive (- fuel 1) :command p p 0 mask fault (cons (list :terminator rcode) events)
                                 slot gen tslot tgen fn2-pool))
                     (,drive (- fuel 1) (if (eq status :terminator) :command mode) p p 0 mask fault
                             (cons (if (eq status :data) (list :data ds de) (list status)) events)
                             slot gen tslot tgen fn2-pool)))))
            (mv-let (status s p o)
              (fn2-gram-frame *fn2-gram-run-bytes* start pos overflow ,cap slot gen 1 1 1 fn2-pool)
              (case status
                ((:need-more) (mv mode s p o events fn2-pool))
                ((:budget) (,drive (- fuel 1) mode s p o mask fault events slot gen tslot tgen fn2-pool))
                ((:line)
                 (mv-let (code0 tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3)
                   (,parse s p mask slot gen 1 1 1 fn2-pool)
                   (let ((code (fn2-gram-fault-code fault code0 tag ,none)))
                    (if (eq code :discard)
                        (,drive (- fuel 1) (list :discard tag) p p 0 mask fault
                                (cons (list :command code tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3 s p :deferred)
                                      events)
                                slot gen tslot tgen fn2-pool)
                     (mv-let (cmd reply0) (,respond code tag)
                       (mv-let (rcode fn2-pool)
                         (,render cmd (fn2-gram-fault-reply fault reply0 ,rsyntax ,runknown)
                                  mask 0 0 0 slot gen s 0 tslot tgen 1 1 1 fn2-pool)
                         (let ((next (cond ((eq code :malformed) (if (eq fault :drop) :command :stopped))
                                           ((not (eq code :ok)) :command)
                                           ((,(fn2-gram-sym g "-hand-off") tag) :stopped)
                                           ((,(fn2-gram-sym g "-block") tag) :block)
                                           (t :command))))
                           (,drive (- fuel 1) next p p 0 mask fault
                                   (cons (list :command code tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3 s p rcode)
                                         events)
                                   slot gen tslot tgen fn2-pool))))))))
                (otherwise
                 (mv-let (rcode fn2-pool)
                   (,render ,none ,rsyntax mask 0 0 0 slot gen 0 0 tslot tgen 1 1 1 fn2-pool)
                   (mv :stopped s p o (cons (list status rcode) events) fn2-pool))))))))
      (defun ,(fn2-gram-sym g "-feed") (k octets slot gen fn2-pool)
        (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix k)))
        (if (or (zp k) (atom octets)) (mv octets fn2-pool)
          (mv-let (code fn2-pool) (fn2-gram-put (nfix (car octets)) slot gen 1 1 1 fn2-pool)
            (declare (ignore code))
            (,(fn2-gram-sym g "-feed") (- k 1) (cdr octets) slot gen fn2-pool))))
      (defun ,(fn2-gram-sym g "-slot-bytes") (k n slot gen fn2-pool)
        (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix (- (nfix n) (nfix k)))))
        (if (>= (nfix k) (nfix n)) nil
          (mv-let (ok b) (fn2-gram-read slot gen (nfix k) 1 1 1 fn2-pool)
            (cons (if ok b :unreadable) (,(fn2-gram-sym g "-slot-bytes") (+ 1 (nfix k)) n slot gen fn2-pool)))))
      (defun ,(fn2-gram-sym g "-chunks") (sizes octets mode start pos overflow mask fault events slot gen tslot tgen fn2-pool)
        (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (len octets)))
        (if (atom octets) (mv mode events fn2-pool)
          (let ((k (if (and (consp sizes) (posp (car sizes))) (car sizes) (len octets))))
            (mv-let (rest fn2-pool) (,(fn2-gram-sym g "-feed") k octets slot gen fn2-pool)
              (mv-let (mode start pos overflow events fn2-pool)
                (,drive (+ 8 (* 4 (len octets))) mode start pos overflow mask fault events slot gen tslot tgen fn2-pool)
                (if (>= (len rest) (len octets)) (mv mode events fn2-pool)
                  (,(fn2-gram-sym g "-chunks") (if (consp sizes) (cdr sizes) nil) rest mode start pos overflow
                                               mask fault events slot gen tslot tgen fn2-pool)))))))
      ;; Events in order, and the rendered reply bytes, for octets arriving in
      ;; chunks of the given sizes (the remainder as one chunk), under FAULT
      ;; (nil, or a mutation control of *fn2-gram-faults*).
      (defun ,run-fault (octets sizes mask fault)
        (declare (xargs :verify-guards nil))
        (with-local-stobj fn2-pool
          (mv-let (result fn2-pool)
            (let ((fn2-pool (fn2-pool-init '((2 . 8192)) 1 1000 fn2-pool)))
              (mv-let (c1 slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
                (mv-let (c2 tslot tgen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
                  (mv-let (mode events fn2-pool)
                    (,(fn2-gram-sym g "-chunks") sizes octets :command 0 0 0 mask fault nil slot gen tslot tgen fn2-pool)
                    (mv (list c1 c2 mode (reverse events)
                              (,(fn2-gram-sym g "-slot-bytes") 0 (fn2-gram-fill tslot fn2-pool) tslot tgen fn2-pool))
                        fn2-pool)))))
            result)))
      (defun ,run (octets sizes mask)
        (declare (xargs :verify-guards nil))
        (,run-fault octets sizes mask nil))
      (make-event (value (fn2-declare '(:operation-set ,g) nil nil nil)))
      (defthm-owed ,(fn2-gram-sym g "-parse-total") (s e mask slot gen okind oslot ogen pool)
        (implies (and (fn2-poolp pool) (fn2-pool-wfp pool) (natp s) (natp e))
                 (,(fn2-gram-sym g "-parse-outcome-p") s e mask slot gen okind oslot ogen pool))
        :schema :invariant :from (:operation-set ,g)
        :teeth (,(fn2-gram-sym g "-test-parse-total") ,(fn2-gram-sym g "-test-parse-total-negative"))
        :doc "Totality over arbitrary octets: under only the pool and index guard, a line parse returns a declared code, a tag within the enum and at most four argument descriptors.")
      (defthm-owed ,(fn2-gram-sym g "-fragmentation") (octets sizes mask)
        (implies (and (fn2-gram-octetsp octets) (< (len octets) 4096) (nat-listp sizes))
                 (equal (,run octets sizes mask) (,run octets nil mask)))
        :schema :invariant :from (:operation-set ,g)
        :teeth (,(fn2-gram-sym g "-test-fragmentation") ,(fn2-gram-sym g "-test-fragmentation-negative"))
        :doc "Fragmentation invariance: every split of a transcript into chunks gives the same parsed commands, block lines and rendered reply bytes.")
      (defthm-owed ,(fn2-gram-sym g "-reply-typing") (cmd reply mask n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen pool)
        (implies (and (fn2-poolp pool) (fn2-pool-wfp pool))
                 (,(fn2-gram-sym g "-render-typed-p") cmd reply mask n0 n1 n2 sslot sgen soff slen slot gen okind oslot ogen pool))
        :schema :invariant :from (:operation-set ,g)
        :teeth (,(fn2-gram-sym g "-test-reply-typing") ,(fn2-gram-sym g "-test-reply-typing-negative"))
        :doc "Reply typing: a reply is rendered only for the command that declares it, in a state its layer admits; its status line opens with the declared code (checked at declaration)."))))

(defun fn2-gram-state-consts (g states bit)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil
    (cons `(defconst ,(fn2-gram-const g "-state-" (car states)) ,(expt 2 bit))
          (fn2-gram-state-consts g (cdr states) (+ 1 bit)))))

; The line parser and the typed renderer of grammar G (split from
; FN2-GRAM-EVENTS, whose admission grows with the size of its body).
(defun fn2-gram-parse-events (g none absent std guard)
  (declare (xargs :verify-guards nil))
  `(
       ; One complete command line [s, e) (its LF at e-1):
       ; (mv code tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3), CODE one of
       ; :ok :malformed :syntax :unknown :state.
       (defun ,(fn2-gram-sym g "-parse-line-0") (s e mask ,@std)
         (declare (xargs :stobjs fn2-pool :guard (and ,guard (natp s) (natp e))))
         (let ((code (fn2-gram-check-line s e ,@std)))
           (if (not (eq code :ok)) (mv code ,none 0 ,@absent)
             (let* ((end (nfix (- e 2)))
                    (te (fn2-gram-skip (nfix (- end s)) s end nil ,@std))
                    (as (fn2-gram-skip (nfix (- end te)) te end t ,@std)))
               (if (and (< as end) (> (- end as) ,(fn2-gram-const g "-args-cap")))
                   (mv :syntax ,none 0 ,@absent)
                 (let ((tag (,(fn2-gram-sym g "-keyword-tag") s (nfix (- te s)) ,@std)))
                   (cond ((equal tag ,none) (mv :unknown tag 0 ,@absent))
                         ((not (and (integerp mask) (logtest mask (,(fn2-gram-sym g "-command-states") tag))))
                          (mv :state tag 0 ,@absent))
                         (t (mv-let (code nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3)
                              (,(fn2-gram-sym g "-args") tag s end ,@std)
                              (mv code tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3))))))))))
       ; A malformed or syntax-refused line of an immediate-block command
       ; whose keyword stands first, admitted in this state, framed
       ; structurally: :discard (its block follows and is discarded).
       (defun ,(fn2-gram-sym g "-parse-line") (s e mask ,@std)
         (declare (xargs :stobjs fn2-pool :guard (and ,guard (natp s) (natp e))))
         (mv-let (code tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3) (,(fn2-gram-sym g "-parse-line-0") s e mask ,@std)
           (if (not (member-eq code '(:malformed :syntax))) (mv code tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3)
             (let* ((end (nfix (- e 2)))
                    (te (fn2-gram-skip (nfix (- end s)) s end nil ,@std))
                    (itag (,(fn2-gram-sym g "-keyword-tag") s (nfix (- te s)) ,@std)))
               (if (and (eq (,(fn2-gram-sym g "-block") itag) :immediate)
                        (integerp mask) (logtest mask (,(fn2-gram-sym g "-command-states") itag))
                        (fn2-gram-structural-p s e ,@std))
                   (mv :discard itag 0 ,@absent)
                 (mv code tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3))))))
       ; Typed rendering: a reply is written only for its own command, in a
       ; state its layer admits; its status code is the declared one.
       (defun ,(fn2-gram-sym g "-render") (cmd reply mask n0 n1 n2 sslot sgen soff slen ,@std)
         (declare (xargs :stobjs fn2-pool
                         :guard (and ,guard (natp n0) (natp n1) (natp n2) (natp soff) (natp slen))))
         (if (not (and (equal (,(fn2-gram-sym g "-reply-command") reply) cmd)
                       (,(fn2-gram-sym g "-reply-admitted") reply mask)))
             (mv :untyped fn2-pool)
           (mv-let (code fn2-pool)
             (fn2-gram-put-template 0 (,(fn2-gram-sym g "-reply-template") reply) 0 n0 n1 n2
                                    sslot sgen soff slen ,@std)
             (if (not (eq code :ok)) (mv code fn2-pool) (fn2-gram-put-crlf ,@std)))))))

(defun fn2-gram-events (g line-cap args-cap block-line-cap states layers fields general commands)
  (declare (xargs :verify-guards nil))
  (let* ((n (len commands))
         (none (fn2-gram-const g "-command-none"))
         (rows (append (fn2-gram-all-reply-rows commands 0)
                       (fn2-gram-reply-rows nil n (cons '(:none :code 500 :text "500 none" :layer :none :class :refused) general))))
         (nreplies (len rows))
         (std '(slot gen okind oslot ogen fn2-pool))
         (guard '(fn2-pool-wfp fn2-pool))
         (absent '(:absent 0 0 :absent 0 0 :absent 0 0 :absent 0 0)))
    `(progn
       (defconst ,(fn2-gram-const g "-line-cap") ,line-cap)
       (defconst ,(fn2-gram-const g "-args-cap") ,args-cap)
       (defconst ,(fn2-gram-const g "-block-line-cap") ,block-line-cap)
       ,@(fn2-gram-command-consts g commands 0)
       (defconst ,none ,n)
       ,@(fn2-gram-reply-consts g rows 0)
       (defconst ,(fn2-gram-const g "-reply-count") ,nreplies)
       ,@(fn2-gram-state-consts g states 0)
       ,@(fn2-gram-declarations g commands)
       (defun ,(fn2-gram-sym g "-keyword-tag") (ts tl ,@std)
         (declare (xargs :stobjs fn2-pool :guard (and ,guard (natp ts) (natp tl))))
         (cond ,@(fn2-gram-keyword-arms g commands) (t ,none)))
       (defun ,(fn2-gram-sym g "-command-states") (tag)
         (declare (xargs :guard t))
         (case tag ,@(fn2-gram-command-arms g commands 0 :states states) (otherwise 0)))
       (defun ,(fn2-gram-sym g "-state-refusal") (tag)
         (declare (xargs :guard t))
         (case tag ,@(fn2-gram-command-arms g commands 0 :refusal states) (otherwise ,(fn2-gram-const g "-reply-none"))))
       (defun ,(fn2-gram-sym g "-block") (tag)
         (declare (xargs :guard t))
         (case tag ,@(fn2-gram-command-arms g commands 0 :block states) (otherwise nil)))
       (defun ,(fn2-gram-sym g "-block-code") (tag)
         (declare (xargs :guard t))
         (case tag ,@(fn2-gram-command-arms g commands 0 :block-code states) (otherwise 0)))
       (defun ,(fn2-gram-sym g "-block-refusal") (tag)
         (declare (xargs :guard t))
         (case tag ,@(fn2-gram-command-arms g commands 0 :block-refusal states) (otherwise ,(fn2-gram-const g "-reply-none"))))
       (defun ,(fn2-gram-sym g "-hand-off") (tag)
         (declare (xargs :guard t))
         (case tag ,@(fn2-gram-command-arms g commands 0 :hand-off states) (otherwise nil)))
       (defun ,(fn2-gram-sym g "-hand-off-code") (tag)
         (declare (xargs :guard t))
         (case tag ,@(fn2-gram-command-arms g commands 0 :hand-off-code states) (otherwise 0)))
       (defun ,(fn2-gram-sym g "-reply-command") (reply)
         (declare (xargs :guard t))
         (case reply ,@(fn2-gram-reply-arms rows 0 :command fields) (otherwise -1)))
       (defun ,(fn2-gram-sym g "-reply-code") (reply)
         (declare (xargs :guard t))
         (case reply ,@(fn2-gram-reply-arms rows 0 :code fields) (otherwise 0)))
       (defun ,(fn2-gram-sym g "-reply-template") (reply)
         (declare (xargs :guard t))
         (case reply ,@(fn2-gram-reply-arms rows 0 :template fields) (otherwise "")))
       (defthm ,(fn2-gram-sym g "-reply-template-stringp") (stringp (,(fn2-gram-sym g "-reply-template") reply))
         :rule-classes :type-prescription)
       (defun ,(fn2-gram-sym g "-reply-layer") (reply)
         (declare (xargs :guard t))
         (case reply ,@(fn2-gram-reply-arms rows 0 :layer fields) (otherwise :none)))
       (defun ,(fn2-gram-sym g "-reply-class") (reply)
         (declare (xargs :guard t))
         (case reply ,@(fn2-gram-reply-arms rows 0 :class fields) (otherwise :refused)))
       ; A reply is admitted when the connection's state mask has the bit its layer needs.
       (defun ,(fn2-gram-sym g "-reply-admitted") (reply mask)
         (declare (xargs :guard t))
         (let ((need (case (,(fn2-gram-sym g "-reply-layer") reply) ,@(fn2-gram-layer-arms layers states) (otherwise 0))))
           (and (integerp mask) (not (equal need 0)) (or (equal need -1) (logtest need mask)))))
       (defun ,(fn2-gram-sym g "-args") (tag s end ,@std)
         (declare (xargs :stobjs fn2-pool :guard (and ,guard (natp s) (natp end))))
         (case tag ,@(fn2-gram-command-arms g commands 0 :args states)
           (otherwise (mv :syntax 0 ,@absent))))
       ,@(fn2-gram-parse-events g none absent std guard)
       (defconst ,(fn2-gram-const g "-help-text") ,(fn2-gram-help-text commands 0))
       (defun ,(fn2-gram-sym g "-first-reply") (tag)
         (declare (xargs :guard t))
         (case tag ,@(fn2-gram-first-reply-arms rows 0 -1) (otherwise ,(fn2-gram-const g "-reply-none"))))
       ,@(fn2-gram-logical-events g))))

(defmacro defgrammar (g &key line-cap args-cap block-line-cap states layers fields general commands)
  (if (and (symbolp g) (posp line-cap) (posp args-cap) (posp block-line-cap)
           (keyword-listp states) (no-duplicatesp-eq states) (<= (len states) 16)
           (fn2-gram-replies-p general) (fn2-gram-commands-p commands states))
      (fn2-gram-events g line-cap args-cap block-line-cap states layers fields general commands)
    (er hard 'defgrammar "Invalid grammar declaration ~x0." g)))
