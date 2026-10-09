; fn: the ARTICLE/HEAD/BODY/STAT wire over spans (landing 2 of the spans
; concept, statements first).
;
; Four `def-span-scan' instances carry the family's served path:
;   fn-nsp-frame        :stream  the command line out of the connection's input,
;                                the wire machine's command mode
;                                (books/wire.lisp fn-wire-feed-byte), one line
;                                per call, into the line workspace;
;   fn-nsp-tokens       :stream  the line's tokens and RFC 3977 section 3.1
;                                preflight (fn-nntp-command-inputp,
;                                fn-nntp-tokenize), one token per yield;
;   fn-nsp-frame-block  :fold    the stored octets' framing (every line CRLF,
;                                no NUL, bare LF or bare CR) and the first
;                                CRLFCRLF, in one pass allocating nothing;
;   fn-nsp-stuff        :stream  the reply block: each line dot-stuffed, the
;                                terminator ".CRLF" at the end.
; The keystones restating the list path's theorems over these instances are
; stated in build/ready/spans-wire-statements.md and enter here when proved.

(in-package "ACL2")
(include-book "def-span-scan")
(include-book "wire-span")
(include-book "nntp-article-pass")
(include-book "wire-outbound-invariants")
(include-book "nntp-responses")
(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; fn-nsp-frame: S is 2N + CR while the line is live (N octets on the line, CR
; set when a CR is pending); a refused frame's state names its reason.

(defconst *fn-nsp-refused-malformed* (expt 2 57))
(defconst *fn-nsp-refused-overlimit* (+ 1 (expt 2 57)))

(defun fn-nsp-frame-step (limit s o)
  (declare (xargs :guard (and (unsigned-byte-p 55 limit) (unsigned-byte-p 59 s)
                              (fn-cbor-octetp o))))
  (let* ((s (nfix s))
         (n (floor s 2))
         (cr (mod s 2)))
    (cond ((<= *fn-nsp-refused-malformed* s) (mv s 0 0 2))
          ((eql cr 1) (if (eql o 10)
                          (mv 0 0 0 1)
                        (mv *fn-nsp-refused-malformed* 0 0 2)))
          ((eql o 13) (mv (+ 1 (* 2 n)) 0 0 0))
          ((eql o 10) (mv *fn-nsp-refused-malformed* 0 0 2))
          ((< n (nfix limit)) (mv (* 2 (+ n 1)) 1 o 0))
          (t (mv *fn-nsp-refused-overlimit* 0 0 2)))))

(defun fn-nsp-frame-final (s)
  (declare (xargs :guard (unsigned-byte-p 59 s)))
  (if (eql s 0) (mv 0 0 0 0) (mv s 0 0 2)))

(def-span-scan fn-nsp-frame (limit)
  :shape :stream
  :state-type (unsigned-byte 59)
  :step (fn-nsp-frame-step limit s o)
  :final (fn-nsp-frame-final s)
  :emit-max 1
  :final-max 0
  :cost-max 1
  :guard (unsigned-byte-p 55 limit))

; -----------------------------------------------------------------------------
; fn-nsp-tokens: S = PHASE + 4*B + 16*C.  PHASE 0 before the first token, 1 in
; a token, 2 in a separator run; B the BOM matcher (EF BB BF); C the octets so
; far.  A refusal answers what fn-nntp-tokenize or fn-nntp-command-inputp
; refuses: a line over 510 octets, a BOM, a byte outside SP/TAB/33..255,
; leading or (at FINAL) trailing white space, the empty line.

(defun fn-nsp-tok-step (s o)
  (declare (xargs :guard (and (unsigned-byte-p 13 s) (fn-cbor-octetp o))))
  (let* ((s (nfix s))
         (phase (mod s 4))
         (b (mod (floor s 4) 4))
         (c2 (+ 1 (floor s 16)))
         (b2 (cond ((eql o 239) 1) ((and (eql b 1) (eql o 187)) 2) (t 0))))
    (cond ((or (< 510 c2) (and (eql b 2) (eql o 191))
               (not (or (eql o 9) (eql o 32) (and (integerp o) (<= 33 o) (<= o 255)))))
           (mv s 0 0 2))
          ((or (eql o 9) (eql o 32))
           (cond ((eql phase 0) (mv s 0 0 2))
                 ((eql phase 1) (mv (+ 2 (* 4 b2) (* 16 c2)) 0 0 1))
                 (t (mv (+ 2 (* 4 b2) (* 16 c2)) 0 0 0))))
          (t (mv (+ 1 (* 4 b2) (* 16 c2)) 1 o 0)))))

(defun fn-nsp-tok-final (s)
  (declare (xargs :guard (unsigned-byte-p 13 s)))
  (if (eql (mod (nfix s) 4) 1) (mv s 0 0 0) (mv s 0 0 2)))

(def-span-scan fn-nsp-tokens ()
  :shape :stream
  :state-type (unsigned-byte 13)
  :step (fn-nsp-tok-step s o)
  :final (fn-nsp-tok-final s)
  :emit-max 1
  :final-max 0
  :cost-max 1)

; The tokens of one pass: the emitted octets split at each :yield, the last
; token closed by the end; none unless the pass is :done.
(defun fn-nsp-split-items (items cur)
  (declare (xargs :guard (true-listp cur)))
  (if (consp items)
      (if (eq (car items) :yield)
          (cons (reverse cur) (fn-nsp-split-items (cdr items) nil))
        (fn-nsp-split-items (cdr items) (cons (car items) cur)))
    (if (consp cur) (list (reverse cur)) nil)))

(defun fn-nsp-tokens-of (r items)
  (declare (xargs :guard t))
  (if (eq r :done) (fn-nsp-split-items items nil) nil))

; -----------------------------------------------------------------------------
; fn-nsp-frame-block: ACC = PEND + 2*START + 4*BAD + 8*M + 64*C.  PEND a CR
; awaits its LF; START the line so far is empty; BAD a framing fault was seen;
; M the CRLFCRLF matcher (books/article-stream.lisp fn-ast-separator-next), 4
; once found; C the octets consumed until then (frozen at the find).

(defconst *fn-nsp-block-init* 2)

(defun fn-nsp-block-next (acc o)
  (declare (xargs :guard (and (unsigned-byte-p 59 acc) (fn-cbor-octetp o))))
  (let* ((acc (nfix acc))
         (pend (mod acc 2))
         (start (mod (floor acc 2) 2))
         (bad (mod (floor acc 4) 2))
         (m (mod (floor acc 8) 8))
         (c (floor acc 64))
         (pend2 (if (and (eql pend 0) (eql o 13)) 1 0))
         (start2 (cond ((eql pend 1) 1) ((eql o 13) start) (t 0)))
         (bad2 (if (or (eql bad 1)
                       (and (eql pend 1) (not (eql o 10)))
                       (and (eql pend 0) (or (eql o 10) (eql o 0))))
                   1 0))
         (m2 (cond ((eql m 4) 4)
                   ((eql m 0) (if (eql o 13) 1 0))
                   ((eql m 1) (cond ((eql o 10) 2) ((eql o 13) 1) (t 0)))
                   ((eql m 2) (if (eql o 13) 3 0))
                   (t (cond ((eql o 10) 4) ((eql o 13) 1) (t 0)))))
         (c2 (if (or (eql m 4) (<= (expt 2 52) (+ 1 c))) c (+ 1 c))))
    (+ pend2 (* 2 start2) (* 4 bad2) (* 8 m2) (* 64 c2))))

(def-span-scan fn-nsp-frame-block ()
  :shape :fold
  :acc-type (unsigned-byte 59)
  :body (fn-nsp-block-next acc o)
  :cost-max 1)

(defun fn-nsp-block-framedp (acc)
  (declare (xargs :guard (natp acc)))
  (and (eql (mod acc 8) 2) (eql (mod (floor acc 8) 8) 4)))

; The header fragment's end (its final CRLF included), from the span's start.
(defun fn-nsp-block-head-end (acc)
  (declare (xargs :guard (natp acc)))
  (nfix (- (floor acc 64) 2)))

(defun fn-nsp-section-start (kind i acc)
  (declare (xargs :guard (and (natp i) (natp acc))))
  (if (eq kind :body) (+ i (fn-nsp-block-head-end acc) 2) i))

(defun fn-nsp-section-end (kind i end acc)
  (declare (xargs :guard (and (natp i) (natp end) (natp acc))))
  (if (eq kind :head) (+ i (fn-nsp-block-head-end acc)) end))

; -----------------------------------------------------------------------------
; fn-nsp-stuff: S is 0 at a line start, 1 within a line.  A line opening with
; "." is sent with ".." (RFC 3977 section 3.1.1); FINAL writes ".CRLF" at a
; line start and refuses an unterminated last line.

(defun fn-nsp-stuff-step (s o)
  (declare (xargs :guard (and (unsigned-byte-p 1 s) (fn-cbor-octetp o))))
  (let ((s2 (if (eql o 10) 0 1)))
    (if (and (eql s 0) (eql o 46))
        (mv s2 2 (+ 46 (* 256 46)) 0)
      (mv s2 1 o 0))))

(defun fn-nsp-stuff-final (s)
  (declare (xargs :guard (unsigned-byte-p 1 s)))
  (if (eql s 0)
      (mv 0 3 (+ 46 (* 256 13) (* 65536 10)) 0)
    (mv s 0 0 2)))

(def-span-scan fn-nsp-stuff ()
  :shape :stream
  :state-type (unsigned-byte 1)
  :step (fn-nsp-stuff-step s o)
  :final (fn-nsp-stuff-final s)
  :emit-max 2
  :final-max 3
  :cost-max 1
  :final-cost-max 1)

; ---- k7a.lsp
(local (defthm fn-nsp-octet-listp-true-listp
  (implies (fn-wire-octet-listp x) (true-listp x))
  :rule-classes :forward-chaining))
(local (defthm fn-nsp-true-listp-render-lines
  (implies (fn-wire-clean-linesp lines)
           (true-listp (fn-wire-render-lines lines)))
  :hints (("Goal" :use fn-wire-render-lines-is-an-octet-list
           :in-theory (disable fn-wire-render-lines-is-an-octet-list)))))
; ---- k7.lsp
(local (defthm fn-nsp-stuff-items-line-start-1
  (implies (fn-wire-line-contentp l)
           (equal (fn-nsp-stuff-items 1 (append l (cons 13 (cons 10 rest))) last)
                  (list (mv-nth 0 (fn-nsp-stuff-items 0 rest last))
                        (mv-nth 1 (fn-nsp-stuff-items 0 rest last))
                        (append l (cons 13 (cons 10 (mv-nth 2 (fn-nsp-stuff-items 0 rest last))))))))
  :hints (("Goal" :induct (fn-wire-line-contentp l)
           :in-theory (enable fn-wire-line-contentp fn-nsp-stuff-items fn-nsp-stuff-step fn-oct-word-octets)))))
; ---- k7b.lsp
(local (defthm fn-nsp-stuff-items-line-start-0
  (implies (fn-wire-line-contentp l)
           (equal (fn-nsp-stuff-items 0 (append l (cons 13 (cons 10 rest))) last)
                  (list (mv-nth 0 (fn-nsp-stuff-items 0 rest last))
                        (mv-nth 1 (fn-nsp-stuff-items 0 rest last))
                        (append (fn-wire-stuff-line l)
                                (cons 13 (cons 10 (mv-nth 2 (fn-nsp-stuff-items 0 rest last))))))))
  :hints (("Goal" :in-theory (e/d (fn-wire-line-contentp fn-nsp-stuff-step fn-wire-stuff-line fn-oct-word-octets)
                                  (fn-nsp-stuff-items-line-start-1))
           :expand ((fn-nsp-stuff-items 0 (append l (cons 13 (cons 10 rest))) last))
           :use ((:instance fn-nsp-stuff-items-line-start-1 (l (cdr l))))))))
(local (defthm fn-nsp-stuff-items-of-lines
  (implies (fn-wire-clean-linesp lines)
           (equal (fn-nsp-stuff-items 0 (fn-wire-source-lines lines) t)
                  (list :done 0 (append (fn-wire-render-lines lines) '(46 13 10)))))
  :hints (("Goal" :induct (fn-wire-clean-linesp lines)
           :in-theory (e/d (fn-wire-clean-linesp fn-wire-source-lines fn-wire-render-lines fn-wire-append
                            fn-nsp-stuff-items fn-nsp-stuff-final fn-oct-word-octets)
                           ())))))
; ---- k7c.lsp
(defthm fn-nsp-stuff-is-the-render-block
  (implies (and (natp i) (natp end) (<= i end) (<= end (fn-octets-len fn-octets))
                (fn-wire-outbound-okp
                 (fn-wire-render-block (fn-oct-slice-list i end fn-octets) limit)))
           (equal (fn-nsp-stuff-items 0 (fn-oct-slice-list i end fn-octets) t)
                  (list :done 0 (fn-wire-outbound-octets
                                 (fn-wire-render-block (fn-oct-slice-list i end fn-octets) limit)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-wire-outbound-lines-success-reconstructs-source
                                   (octets (fn-oct-slice-list i end fn-octets)))
                        (:instance fn-wire-outbound-lines-success-is-clean
                                   (octets (fn-oct-slice-list i end fn-octets)))
                        (:instance fn-wire-successful-render-block-octets
                                   (article (fn-oct-slice-list i end fn-octets)))
                        (:instance fn-nsp-stuff-items-of-lines
                                   (lines (fn-wire-outbound-octets
                                           (fn-wire-outbound-lines (fn-oct-slice-list i end fn-octets) limit)))))
           :in-theory (disable fn-nsp-stuff-items-of-lines fn-wire-outbound-lines-success-is-clean
                               fn-wire-outbound-lines-success-reconstructs-source
                               fn-wire-successful-render-block-octets fn-wire-render-block))))
; ---- k8.lsp
(local (defthm fn-nsp-len-of-slice
  (implies (and (natp i) (natp end) (<= i end))
           (equal (len (fn-oct-slice-list i end fn-octets)) (- end i)))
  :hints (("Goal" :induct (fn-oct-slice-list i end fn-octets)
           :in-theory (enable fn-oct-slice-list)))))
(local (defthm fn-nsp-consp-of-slice
  (implies (and (natp i) (natp end) (< i end))
           (consp (fn-oct-slice-list i end fn-octets)))
  :hints (("Goal" :expand ((fn-oct-slice-list i end fn-octets))))))
(local (defthm fn-nsp-stuff-is-the-render-block-rw
  (implies (and (natp i) (natp end) (<= i end) (<= end (fn-octets-len fn-octets))
                (fn-wire-outbound-okp
                 (fn-wire-render-block (fn-oct-slice-list i end fn-octets) limit)))
           (equal (fn-nsp-stuff-items 0 (fn-oct-slice-list i end fn-octets) t)
                  (list :done 0 (fn-wire-outbound-octets
                                 (fn-wire-render-block (fn-oct-slice-list i end fn-octets) limit)))))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :use fn-nsp-stuff-is-the-render-block))))
(defthm fn-nsp-drive-of-span-rendered-article-preserves-source
  (implies
   (and (posp command-limit)
        (natp i) (natp end) (< i end) (<= end (fn-octets-len fn-octets))
        (fn-wire-outbound-okp
         (fn-wire-render-block (fn-oct-slice-list i end fn-octets) article-limit))
        (<= (nfix article-limit) (nfix body-limit)))
   (let ((lines (fn-wire-outbound-octets
                 (fn-wire-outbound-lines (fn-oct-slice-list i end fn-octets) article-limit))))
     (mv-let (r s2 items) (fn-nsp-stuff-items 0 (fn-oct-slice-list i end fn-octets) t)
       (declare (ignore s2))
       (and (equal r :done)
            (equal
             (fn-wire-drive
              (fn-wire-result-state
               (fn-wire-begin-article-with-line-limit
                (fn-wire-initial-state command-limit body-limit)
                (fn-wire-article-line-limit
                 (fn-wire-initial-state command-limit body-limit))))
              items)
             (fn-wire-make-result
              (fn-wire-make-state :command nil 0 nil nil 0
                                  (+ 1 (nfix body-limit))
                                  (nfix body-limit))
              (list (fn-wire-article-event lines))))
            (equal (fn-wire-source-lines lines) (fn-oct-slice-list i end fn-octets))))))
  :rule-classes nil
  :hints (("Goal"
           :use (                 (:instance fn-nsp-len-of-slice)
                 (:instance fn-wire-nonempty-successful-render-block-needs-positive-body-limit
                            (article (fn-oct-slice-list i end fn-octets)))
                 (:instance fn-wire-served-article-profile-is-outbound-receiver-start)
                 (:instance fn-wire-drive-of-successful-render-block-preserves-source
                            (article (fn-oct-slice-list i end fn-octets))
                            (limit article-limit)))
           :in-theory (disable fn-nsp-len-of-slice
                               fn-wire-served-article-profile-is-outbound-receiver-start
                               fn-wire-drive fn-wire-render-block fn-wire-outbound-lines
                               fn-oct-slice-list)
           :do-not '(generalize fertilize))))
; ---- ks-defs.lsp
; Landing 2's restated keystones, as statements (translated, not proved).
(defun fn-nsp-frame-wsp (r s2 i2 out2 ws)
  (let ((ll (fn-wire-state-line-limit ws)) (bl (fn-wire-state-body-limit ws)))
    (cond ((eq r :yield)
           (fn-wsp-make (fn-wire-make-state :command nil 0 nil nil 0 ll bl)
                        (list (fn-wire-command-event out2)) i2))
          ((eq r :refused)
           (fn-wsp-make (fn-wire-make-state :closed nil 0 nil nil 0 ll bl)
                        (list (fn-wire-reject-event
                               (if (equal s2 *fn-nsp-refused-overlimit*) :line-overlimit :malformed)))
                        (+ 1 i2)))
          (t (fn-wsp-make (fn-wire-make-state :command (fn-wire-reverse-octets out2) (len out2) nil
                                              (if (equal (mod s2 2) 1) t nil) 0 ll bl)
                          nil i2)))))
(defun fn-nsp-frame-state-of (ws)
  (+ (* 2 (nfix (fn-wire-state-line-len ws))) (if (fn-wire-state-pending-crp ws) 1 0)))
; ---- k2.lsp
(local (defun fn-nsp-tk-st (ph b c) (+ ph (* 4 b) (* 16 c))))
(local (defthm fn-nsp-tk-st-ph
  (implies (and (natp ph) (< ph 4) (natp b) (< b 4) (natp c))
           (equal (mod (fn-nsp-tk-st ph b c) 4) ph))
  :hints (("Goal" :in-theory (enable fn-nsp-tk-st)))))
(local (defthm fn-nsp-tk-st-b
  (implies (and (natp ph) (< ph 4) (natp b) (< b 4) (natp c))
           (equal (mod (floor (fn-nsp-tk-st ph b c) 4) 4) b))
  :hints (("Goal" :in-theory (enable fn-nsp-tk-st)))))
(local (defthm fn-nsp-tk-st-c
  (implies (and (natp ph) (< ph 4) (natp b) (< b 4) (natp c))
           (equal (floor (fn-nsp-tk-st ph b c) 16) c))
  :hints (("Goal" :in-theory (enable fn-nsp-tk-st)))))
; ---- k2b.lsp
(local (defun fn-nsp-tk-bpre (b) (cond ((eql b 1) '(239)) ((eql b 2) '(239 187)) (t nil))))
(local (defun fn-nsp-tk-b2 (b o) (cond ((eql o 239) 1) ((and (eql b 1) (eql o 187)) 2) (t 0))))
(local (defthm fn-nsp-tk-bom-step
  (implies (and (natp b) (< b 3))
           (equal (fn-nntp-contains-bomp (append (fn-nsp-tk-bpre b) (cons o rest)))
                  (or (and (eql b 2) (eql o 191))
                      (fn-nntp-contains-bomp (append (fn-nsp-tk-bpre (fn-nsp-tk-b2 b o)) rest)))))
  :hints (("Goal" :in-theory (enable fn-nsp-tk-bpre fn-nsp-tk-b2 fn-nntp-contains-bomp fn-nntp-bom-at-startp)))))
(local (defthm fn-nsp-tk-bom-step-xs
  (implies (and (natp b) (< b 3) (consp xs))
           (equal (fn-nntp-contains-bomp (append (fn-nsp-tk-bpre b) xs))
                  (or (and (eql b 2) (eql (car xs) 191))
                      (fn-nntp-contains-bomp (append (fn-nsp-tk-bpre (fn-nsp-tk-b2 b (car xs))) (cdr xs))))))
  :hints (("Goal" :use ((:instance fn-nsp-tk-bom-step (o (car xs)) (rest (cdr xs))))))))
(local (defthm fn-nsp-tk-bpre-no-bom
  (implies (and (natp b) (< b 3))
           (not (fn-nntp-contains-bomp (fn-nsp-tk-bpre b))))
  :hints (("Goal" :in-theory (enable fn-nsp-tk-bpre fn-nntp-contains-bomp fn-nntp-bom-at-startp)))))
(local (defthm fn-nsp-tk-last-nonconsp
  (implies (not (consp x)) (equal (fn-nntp-last x) nil))
  :hints (("Goal" :in-theory (enable fn-nntp-last)))))
(local (defthm fn-nsp-tk-last-consp-1
  (implies (and (consp xs) (consp (cdr xs)))
           (equal (fn-nntp-last xs) (fn-nntp-last (cdr xs))))
  :hints (("Goal" :in-theory (enable fn-nntp-last)))))
(local (defthm fn-nsp-tk-last-consp-2
  (implies (and (consp xs) (not (consp (cdr xs))))
           (equal (fn-nntp-last xs) (car xs)))
  :hints (("Goal" :in-theory (enable fn-nntp-last)))))
; ---- k2d.lsp
(local (defthm fn-nsp-tk-st-natp
  (implies (and (natp ph) (natp b) (natp c)) (natp (fn-nsp-tk-st ph b c)))
  :rule-classes (:rewrite :type-prescription)))
(local (defthm fn-nsp-tk-step-st
  (implies (and (natp ph) (<= ph 2) (natp b) (<= b 2) (natp c))
           (equal (fn-nsp-tok-step (fn-nsp-tk-st ph b c) o)
                  (cond ((or (< 510 (+ 1 c)) (and (eql b 2) (eql o 191))
                             (not (or (eql o 9) (eql o 32) (and (integerp o) (<= 33 o) (<= o 255)))))
                         (list (fn-nsp-tk-st ph b c) 0 0 2))
                        ((or (eql o 9) (eql o 32))
                         (cond ((eql ph 0) (list (fn-nsp-tk-st ph b c) 0 0 2))
                               ((eql ph 1) (list (fn-nsp-tk-st 2 (fn-nsp-tk-b2 b o) (+ 1 c)) 0 0 1))
                               (t (list (fn-nsp-tk-st 2 (fn-nsp-tk-b2 b o) (+ 1 c)) 0 0 0))))
                        (t (list (fn-nsp-tk-st 1 (fn-nsp-tk-b2 b o) (+ 1 c)) 1 o 0)))))
  :hints (("Goal" :in-theory (e/d (fn-nsp-tok-step fn-nsp-tk-b2) (fn-nsp-tk-st))
           :do-not-induct t)
          (and stable-under-simplificationp '(:in-theory (e/d (fn-nsp-tok-step fn-nsp-tk-b2 fn-nsp-tk-st)))))))
(local (defthm fn-nsp-tk-final-st
  (implies (and (natp ph) (<= ph 2) (natp b) (<= b 2) (natp c))
           (equal (fn-nsp-tok-final (fn-nsp-tk-st ph b c))
                  (if (eql ph 1) (list (fn-nsp-tk-st ph b c) 0 0 0) (list (fn-nsp-tk-st ph b c) 0 0 2))))
  :hints (("Goal" :in-theory (e/d (fn-nsp-tok-final) (fn-nsp-tk-st))))))
; ---- k2c-defs.lsp
(local (defun fn-nsp-tk-acc (ph b c xs)
  (and (<= (+ c (len xs)) 510)
       (fn-nntp-command-linep xs)
       (not (fn-nntp-contains-bomp (append (fn-nsp-tk-bpre b) xs)))
       (if (consp xs)
           (and (not (and (eql ph 0) (fn-nntp-space-or-tabp (car xs))))
                (not (fn-nntp-space-or-tabp (fn-nntp-last xs))))
         (eql ph 1)))))
(local (defun fn-nsp-tk-ind (ph b c xs)
  (if (consp xs)
      (fn-nsp-tk-ind (if (fn-nntp-space-or-tabp (car xs)) 2 1) (fn-nsp-tk-b2 b (car xs)) (+ 1 c) (cdr xs))
    (list ph b c))))
; ---- k2c-thm.lsp
(local (defthm fn-nsp-tk-b2-range
  (and (natp (fn-nsp-tk-b2 b o)) (<= (fn-nsp-tk-b2 b o) 2))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (fn-nsp-tk-b2 b o))))))
(local (defthm fn-nsp-tk-done-iff-acc
  (implies (and (natp ph) (<= ph 2) (natp b) (<= b 2) (natp c) (<= c 510) (true-listp xs))
           (iff (equal (mv-nth 0 (fn-nsp-tokens-items (fn-nsp-tk-st ph b c) xs t)) :done)
                (fn-nsp-tk-acc ph b c xs)))
  :hints (("Goal" :induct (fn-nsp-tk-ind ph b c xs)
           :in-theory (e/d (fn-nsp-tokens-items fn-nsp-tk-acc
                            fn-nntp-command-linep fn-nntp-command-bytep fn-nntp-space-or-tabp
                            fn-oct-word-octets)
                           (fn-nsp-tk-st fn-nsp-tok-step fn-nsp-tok-final fn-nsp-tk-bpre fn-nsp-tk-b2
                            fn-nntp-contains-bomp fn-nntp-last)))
          ("Subgoal *1/1" :cases ((consp (cdr xs)))))))
; ---- k2e.lsp
(local (defun fn-nsp-tk-split-ind (ph b c xs word-rev words-rev)
  (if (consp xs)
      (if (fn-nntp-space-or-tabp (car xs))
          (fn-nsp-tk-split-ind 2 (fn-nsp-tk-b2 b (car xs)) (+ 1 c) (cdr xs) nil
                               (if (consp word-rev) (cons (reverse word-rev) words-rev) words-rev))
        (fn-nsp-tk-split-ind 1 (fn-nsp-tk-b2 b (car xs)) (+ 1 c) (cdr xs) (cons (car xs) word-rev) words-rev))
    (list ph b c word-rev words-rev))))
(local (defthm fn-nsp-tk-reverse-cons
  (implies (true-listp x)
           (equal (reverse (cons a x)) (append (reverse x) (list a))))))
(local (defthm fn-nsp-tk-split
  (implies (and (natp ph) (<= ph 2) (natp b) (<= b 2) (natp c) (<= c 510) (true-listp xs)
                (true-listp word-rev) (true-listp words-rev)
                (iff (consp word-rev) (eql ph 1))
                (equal (mv-nth 0 (fn-nsp-tokens-items (fn-nsp-tk-st ph b c) xs t)) :done))
           (equal (fn-nntp-tokenize-aux xs word-rev words-rev)
                  (append (reverse words-rev)
                          (fn-nsp-split-items
                           (mv-nth 2 (fn-nsp-tokens-items (fn-nsp-tk-st ph b c) xs t))
                           word-rev))))
  :hints (("Goal" :induct (fn-nsp-tk-split-ind ph b c xs word-rev words-rev)
           :in-theory (e/d (fn-nsp-tokens-items fn-nntp-tokenize-aux fn-nsp-split-items
                            fn-nntp-space-or-tabp fn-oct-word-octets)
                           (fn-nsp-tk-st fn-nsp-tok-step fn-nsp-tok-final fn-nsp-tk-b2))))))
; ---- k2f.lsp
(local (defthm fn-nsp-tk-octet-list-true-listp
  (implies (fn-octet-listp x) (true-listp x))
  :rule-classes :forward-chaining))
(local (defthm fn-nsp-tk-at-most-is-len
  (implies (natp n)
           (iff (fn-cbor-at-mostp xs n) (<= (len xs) n)))))
(local (defthm fn-nsp-tk-acc-top
  (iff (fn-nsp-tk-acc 0 0 0 line)
       (and (fn-nntp-command-inputp line)
            (consp line)
            (not (fn-nntp-space-or-tabp (car line)))
            (not (fn-nntp-space-or-tabp (fn-nntp-last line)))))
  :hints (("Goal" :use ((:instance fn-nsp-tk-at-most-is-len (xs line) (n 510)))
           :in-theory (e/d (fn-nsp-tk-acc fn-nntp-command-inputp fn-nsp-tk-bpre)
                           (fn-nsp-tk-at-most-is-len fn-nntp-last fn-nntp-space-or-tabp))))))
(local (defthm fn-nsp-tk-tokenize-accepted
  (implies (fn-nsp-tk-acc 0 0 0 line)
           (equal (fn-nntp-tokenize line) (fn-nntp-tokenize-aux line nil nil)))
  :hints (("Goal" :use fn-nsp-tk-acc-top
           :in-theory (e/d (fn-nntp-tokenize fn-nntp-command-inputp)
                           (fn-nsp-tk-acc-top fn-nsp-tk-acc fn-nntp-tokenize-aux fn-nntp-last fn-nntp-space-or-tabp))))))
(local (defthm fn-nsp-tk-tokenize-rejected
  (implies (and (not (fn-nsp-tk-acc 0 0 0 line)) (fn-nntp-command-inputp line))
           (not (fn-nntp-tokenize line)))
  :hints (("Goal" :use fn-nsp-tk-acc-top
           :in-theory (e/d (fn-nntp-tokenize)
                           (fn-nsp-tk-acc-top fn-nsp-tk-acc fn-nntp-tokenize-aux fn-nntp-last fn-nntp-space-or-tabp
                            fn-nntp-command-inputp))))))
(defthm fn-nsp-tokens-is-tokenize
  (implies (fn-octet-listp line)
           (mv-let (r s2 items) (fn-nsp-tokens-items 0 line t)
             (declare (ignore s2))
             (equal (fn-nsp-tokens-of r items)
                    (and (fn-nntp-command-inputp line) (fn-nntp-tokenize line)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-nsp-tk-done-iff-acc (ph 0) (b 0) (c 0) (xs line))
                        (:instance fn-nsp-tk-split (ph 0) (b 0) (c 0) (xs line) (word-rev nil) (words-rev nil))
                        fn-nsp-tk-acc-top fn-nsp-tk-tokenize-accepted fn-nsp-tk-tokenize-rejected)
           :in-theory (e/d (fn-nsp-tokens-of)
                           (fn-nsp-tk-done-iff-acc fn-nsp-tk-split fn-nsp-tk-acc-top fn-nsp-tk-acc
                            fn-nsp-tk-tokenize-accepted fn-nsp-tk-tokenize-rejected
                            fn-nntp-command-inputp fn-nntp-tokenize fn-nntp-tokenize-aux fn-nsp-tokens-items
                            fn-nsp-split-items fn-nntp-last fn-nntp-space-or-tabp)))))
; ---- k3a.lsp
(local (defun fn-nsp-nb-acc (p s bd m c) (+ p (* 2 s) (* 4 bd) (* 8 m) (* 64 c))))
(local (defmacro fn-nsp-nb-bitsp (p s bd m c)
  `(and (natp ,p) (<= ,p 1) (natp ,s) (<= ,s 1) (natp ,bd) (<= ,bd 1) (natp ,m) (<= ,m 4) (natp ,c))))
(local (defthm fn-nsp-nb-acc-natp
  (implies (fn-nsp-nb-bitsp p s bd m c) (natp (fn-nsp-nb-acc p s bd m c)))
  :rule-classes (:rewrite :type-prescription)))
(local (defthm fn-nsp-nb-acc-p
  (implies (fn-nsp-nb-bitsp p s bd m c) (equal (mod (fn-nsp-nb-acc p s bd m c) 2) p))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-acc)))))
(local (defthm fn-nsp-nb-acc-s
  (implies (fn-nsp-nb-bitsp p s bd m c) (equal (mod (floor (fn-nsp-nb-acc p s bd m c) 2) 2) s))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-acc) :cases ((equal p 0) (equal p 1))))))
(local (defthm fn-nsp-nb-acc-bd
  (implies (fn-nsp-nb-bitsp p s bd m c) (equal (mod (floor (fn-nsp-nb-acc p s bd m c) 4) 2) bd))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-acc) :cases ((equal p 0) (equal p 1) (equal s 0) (equal s 1))))))
(local (defthm fn-nsp-nb-acc-m
  (implies (fn-nsp-nb-bitsp p s bd m c) (equal (mod (floor (fn-nsp-nb-acc p s bd m c) 8) 8) m))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-acc)))))
(local (defthm fn-nsp-nb-acc-c
  (implies (fn-nsp-nb-bitsp p s bd m c) (equal (floor (fn-nsp-nb-acc p s bd m c) 64) c))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-acc)))))
(local (defun fn-nsp-nb-pf (acc) (mod acc 2)))
(local (defun fn-nsp-nb-sf (acc) (mod (floor acc 2) 2)))
(local (defun fn-nsp-nb-bdf (acc) (mod (floor acc 4) 2)))
(local (defun fn-nsp-nb-mf (acc) (mod (floor acc 8) 8)))
(local (defun fn-nsp-nb-cf (acc) (floor acc 64)))
(local (defthm fn-nsp-nb-pf-acc (implies (fn-nsp-nb-bitsp p s bd m c) (equal (fn-nsp-nb-pf (fn-nsp-nb-acc p s bd m c)) p))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-pf)))))
(local (defthm fn-nsp-nb-sf-acc (implies (fn-nsp-nb-bitsp p s bd m c) (equal (fn-nsp-nb-sf (fn-nsp-nb-acc p s bd m c)) s))
  :hints (("Goal" :in-theory (e/d (fn-nsp-nb-sf) (fn-nsp-nb-acc-s)) :use fn-nsp-nb-acc-s))))
(local (defthm fn-nsp-nb-bdf-acc (implies (fn-nsp-nb-bitsp p s bd m c) (equal (fn-nsp-nb-bdf (fn-nsp-nb-acc p s bd m c)) bd))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-bdf)))))
(local (defthm fn-nsp-nb-mf-acc (implies (fn-nsp-nb-bitsp p s bd m c) (equal (fn-nsp-nb-mf (fn-nsp-nb-acc p s bd m c)) m))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-mf)))))
(local (defthm fn-nsp-nb-cf-acc (implies (fn-nsp-nb-bitsp p s bd m c) (equal (fn-nsp-nb-cf (fn-nsp-nb-acc p s bd m c)) c))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-cf)))))
(local (in-theory (disable fn-nsp-nb-pf fn-nsp-nb-sf fn-nsp-nb-bdf fn-nsp-nb-mf fn-nsp-nb-cf)))
; ---- k3b.lsp
(local (defun fn-nsp-nb-p2 (p o) (if (and (eql p 0) (eql o 13)) 1 0)))
(local (defun fn-nsp-nb-s2 (p s o) (cond ((eql p 1) 1) ((eql o 13) s) (t 0))))
(local (defun fn-nsp-nb-bd2 (p bd o)
  (if (or (eql bd 1) (and (eql p 1) (not (eql o 10))) (and (eql p 0) (or (eql o 10) (eql o 0)))) 1 0)))
(local (defun fn-nsp-nb-m2 (m o)
  (cond ((eql m 4) 4)
        ((eql m 0) (if (eql o 13) 1 0))
        ((eql m 1) (cond ((eql o 10) 2) ((eql o 13) 1) (t 0)))
        ((eql m 2) (if (eql o 13) 3 0))
        (t (cond ((eql o 10) 4) ((eql o 13) 1) (t 0))))))
(local (defun fn-nsp-nb-c2 (m c) (if (eql m 4) c (+ 1 c))))
(local (defthm fn-nsp-nb-m2-range
  (implies (and (natp m) (<= m 4))
           (and (natp (fn-nsp-nb-m2 m o)) (<= (fn-nsp-nb-m2 m o) 4)))
  :rule-classes ((:rewrite))))
(local (defthm fn-nsp-nb-bits2
  (implies (fn-nsp-nb-bitsp p s bd m c)
           (fn-nsp-nb-bitsp (fn-nsp-nb-p2 p o) (fn-nsp-nb-s2 p s o) (fn-nsp-nb-bd2 p bd o)
                            (fn-nsp-nb-m2 m o) (fn-nsp-nb-c2 m c)))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-p2 fn-nsp-nb-s2 fn-nsp-nb-bd2 fn-nsp-nb-m2 fn-nsp-nb-c2)))))
(local (defthm fn-nsp-nb-step
  (implies (and (fn-nsp-nb-bitsp p s bd m c) (< (+ 1 c) (expt 2 52)))
           (equal (fn-nsp-block-next (fn-nsp-nb-acc p s bd m c) o)
                  (fn-nsp-nb-acc (fn-nsp-nb-p2 p o) (fn-nsp-nb-s2 p s o) (fn-nsp-nb-bd2 p bd o)
                                 (fn-nsp-nb-m2 m o) (fn-nsp-nb-c2 m c))))
  :hints (("Goal" :in-theory (e/d (fn-nsp-block-next fn-nsp-nb-p2 fn-nsp-nb-s2 fn-nsp-nb-bd2 fn-nsp-nb-m2 fn-nsp-nb-c2)
                                  (fn-nsp-nb-acc))
           :cases ((equal p 0) (equal s 0) (equal bd 0) (equal m 0) (equal m 1) (equal m 2) (equal m 3)))
          (and stable-under-simplificationp '(:in-theory (enable fn-nsp-nb-acc))))))
; ---- k3c.lsp
(local (defun fn-nsp-nb-ind (p s bd m c xs)
  (if (consp xs)
      (fn-nsp-nb-ind (fn-nsp-nb-p2 p (car xs)) (fn-nsp-nb-s2 p s (car xs)) (fn-nsp-nb-bd2 p bd (car xs))
                     (fn-nsp-nb-m2 m (car xs)) (fn-nsp-nb-c2 m c) (cdr xs))
    (list p s bd m c))))
(local (defthm fn-nsp-nb-list-step
  (implies (and (fn-nsp-nb-bitsp p s bd m c) (< (+ 1 c) (expt 2 52)) (consp xs))
           (equal (fn-nsp-frame-block-list (fn-nsp-nb-acc p s bd m c) xs)
                  (fn-nsp-frame-block-list
                   (fn-nsp-nb-acc (fn-nsp-nb-p2 p (car xs)) (fn-nsp-nb-s2 p s (car xs)) (fn-nsp-nb-bd2 p bd (car xs))
                                  (fn-nsp-nb-m2 m (car xs)) (fn-nsp-nb-c2 m c))
                   (cdr xs))))
  :hints (("Goal" :expand ((fn-nsp-frame-block-list (fn-nsp-nb-acc p s bd m c) xs))
           :do-not-induct t
           :in-theory (disable fn-nsp-nb-acc fn-nsp-nb-p2 fn-nsp-nb-s2 fn-nsp-nb-bd2 fn-nsp-nb-m2 fn-nsp-nb-c2
                               fn-nsp-frame-block-list)))))
(local (defthm fn-nsp-nb-list-nil
  (implies (not (consp xs)) (equal (fn-nsp-frame-block-list acc xs) acc))
  :hints (("Goal" :in-theory (enable fn-nsp-frame-block-list)))))
(local (in-theory (disable fn-nsp-frame-block-list)))
(local (defthm fn-nsp-nb-c2-bound
  (implies (and (natp c) (consp xs) (< (+ c (len xs)) 4503599627370496))
           (< (+ (fn-nsp-nb-c2 m c) (len (cdr xs))) 4503599627370496))
  :hints (("Goal" :expand ((len xs)) :in-theory (enable fn-nsp-nb-c2)))))
(local (defthm fn-nsp-nb-c2-bound-2
  (implies (and (natp c) (consp xs) (< (+ c (len xs)) 4503599627370496))
           (< (+ (len (cdr xs)) (fn-nsp-nb-c2 m c)) 4503599627370496))
  :hints (("Goal" :expand ((len xs)) :in-theory (enable fn-nsp-nb-c2)))))
(local (defthm fn-nsp-nb-bad-sticky
  (implies (and (fn-nsp-nb-bitsp p s 1 m c) (< (+ c (len xs)) (expt 2 52)))
           (equal (fn-nsp-nb-bdf (fn-nsp-frame-block-list (fn-nsp-nb-acc p s 1 m c) xs)) 1))
  :hints (("Goal" :induct (fn-nsp-nb-ind p s 1 m c xs)
           :in-theory (disable fn-nsp-nb-acc fn-nsp-nb-p2 fn-nsp-nb-s2 fn-nsp-nb-bd2 fn-nsp-nb-m2 fn-nsp-nb-c2))
          (and stable-under-simplificationp
               '(:in-theory (enable fn-nsp-nb-bd2))))))
; ---- k3d.lsp
(local (defthm fn-nsp-validp-13
  (equal (fn-nntp-crlf-validp (cons 13 xs) st)
         (and (consp xs) (equal (car xs) 10) (fn-nntp-crlf-validp (cdr xs) t)))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf-validp)))))
(local (defthm fn-nsp-validp-13-cons
  (implies (and (consp xs) (equal (car xs) 13))
           (equal (fn-nntp-crlf-validp xs st)
                  (and (consp (cdr xs)) (equal (car (cdr xs)) 10) (fn-nntp-crlf-validp (cdr (cdr xs)) t))))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf-validp)))))
(local (defthm fn-nsp-validp-other
  (implies (and (consp xs) (not (equal (car xs) 13)))
           (equal (fn-nntp-crlf-validp xs st)
                  (if (or (equal (car xs) 10) (equal (car xs) 0)) nil (fn-nntp-crlf-validp (cdr xs) nil))))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf-validp)))))
(local (defthm fn-nsp-validp-nil
  (implies (not (consp xs)) (equal (fn-nntp-crlf-validp xs st) (if st t nil)))
  :hints (("Goal" :in-theory (enable fn-nntp-crlf-validp)))))
(local (in-theory (disable fn-nntp-crlf-validp)))
(local (defthm fn-nsp-nb-flags
  (implies (and (fn-nsp-nb-bitsp p s 0 m c) (< (+ c (len xs)) (expt 2 52)) (true-listp xs))
           (iff (let ((r (fn-nsp-frame-block-list (fn-nsp-nb-acc p s 0 m c) xs)))
                  (and (eql (fn-nsp-nb-pf r) 0) (eql (fn-nsp-nb-sf r) 1) (eql (fn-nsp-nb-bdf r) 0)))
                (fn-nntp-crlf-validp (if (eql p 1) (cons 13 xs) xs) (eql s 1))))
  :hints (("Goal" :induct (fn-nsp-nb-ind p s 0 m c xs)
           :in-theory (e/d ()
                           (fn-nsp-nb-acc fn-nsp-nb-p2 fn-nsp-nb-s2 fn-nsp-nb-bd2 fn-nsp-nb-m2 fn-nsp-nb-c2)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-nsp-nb-bd2 fn-nsp-nb-p2 fn-nsp-nb-s2)
                                 (fn-nsp-nb-acc fn-nsp-nb-m2 fn-nsp-nb-c2)))))))
; ---- k3e.lsp
(local (defun fn-nsp-pat (m)
  (cond ((eql m 1) (list 13)) ((eql m 2) (list 13 10)) ((eql m 3) (list 13 10 13))
        ((eql m 4) (list 13 10 13 10)) (t nil))))
(local (defun fn-nsp-sep (xs)
  (cond ((and (consp xs) (consp (cdr xs)) (consp (cddr xs)) (consp (cdddr xs))
              (equal (car xs) 13) (equal (cadr xs) 10) (equal (caddr xs) 13) (equal (cadddr xs) 10))
         4)
        ((consp xs) (let ((r (fn-nsp-sep (cdr xs)))) (and r (+ 1 r))))
        (t nil))))
(local (defthm fn-nsp-sep-type
  (or (null (fn-nsp-sep xs)) (natp (fn-nsp-sep xs)))
  :rule-classes :type-prescription))
(local (defthm fn-nsp-sep-iff-blank
  (iff (fn-nsp-sep xs) (fn-nntp-blank-linep xs))
  :hints (("Goal" :in-theory (enable fn-nntp-blank-linep)))))
(local (in-theory (disable fn-nsp-sep-iff-blank)))
(local (defthm fn-nsp-sep-natp
  (implies (fn-nsp-sep xs) (and (natp (fn-nsp-sep xs)) (<= 4 (fn-nsp-sep xs)) (<= (fn-nsp-sep xs) (len xs))))
  :rule-classes ((:rewrite))))
(local (defthm fn-nsp-sep-step
  (implies (and (natp m) (<= m 3))
           (equal (fn-nsp-sep (append (fn-nsp-pat m) (cons o rest)))
                  (let ((e2 (fn-nsp-sep (append (fn-nsp-pat (fn-nsp-nb-m2 m o)) rest))))
                    (and e2 (+ e2 (- (+ m 1) (fn-nsp-nb-m2 m o)))))))
  :hints (("Goal" :cases ((equal m 0) (equal m 1) (equal m 2) (equal m 3)))
          (and stable-under-simplificationp
               '(:cases ((equal o 13) (equal o 10)) :in-theory (enable fn-nsp-nb-m2 fn-nsp-pat fn-nsp-sep))))))
(local (defthm fn-nsp-sep-pat4
  (equal (fn-nsp-sep (append (fn-nsp-pat 4) xs)) 4)
  :hints (("Goal" :in-theory (enable fn-nsp-pat fn-nsp-sep)))))
(local (defthm fn-nsp-sep-pat-nil
  (implies (and (natp m) (<= m 3)) (not (fn-nsp-sep (fn-nsp-pat m))))
  :hints (("Goal" :cases ((equal m 0) (equal m 1) (equal m 2) (equal m 3))
           :in-theory (enable fn-nsp-pat fn-nsp-sep)))))
(local (defthm fn-nsp-nb-q-step
  (implies (and (natp m) (<= m 4) (natp c) (consp xs)
                (if (fn-nsp-sep (append (fn-nsp-pat (fn-nsp-nb-m2 m (car xs))) (cdr xs)))
                    (and (equal mfv 4)
                         (equal cfv (+ (fn-nsp-nb-c2 m c)
                                       (- (fn-nsp-sep (append (fn-nsp-pat (fn-nsp-nb-m2 m (car xs))) (cdr xs)))
                                          (fn-nsp-nb-m2 m (car xs))))))
                  (and (< mfv 4) (equal cfv (+ (fn-nsp-nb-c2 m c) (len (cdr xs)))))))
           (if (fn-nsp-sep (append (fn-nsp-pat m) xs))
               (and (equal mfv 4) (equal cfv (+ c (- (fn-nsp-sep (append (fn-nsp-pat m) xs)) m))))
             (and (< mfv 4) (equal cfv (+ c (len xs))))))
  :hints (("Goal" :cases ((equal m 4))
           :use ((:instance fn-nsp-sep-step (o (car xs)) (rest (cdr xs))))
           :expand ((len xs))
           :in-theory (e/d (fn-nsp-nb-c2) (fn-nsp-sep-step fn-nsp-pat fn-nsp-nb-m2)))
          (and stable-under-simplificationp
               '(:in-theory (enable fn-nsp-nb-m2 fn-nsp-pat))))))
(local (defthm fn-nsp-nb-match
  (implies (and (fn-nsp-nb-bitsp p s bd m c) (< (+ c (len xs)) 4503599627370496) (true-listp xs))
           (let ((r (fn-nsp-frame-block-list (fn-nsp-nb-acc p s bd m c) xs))
                 (e (fn-nsp-sep (append (fn-nsp-pat m) xs))))
             (if e
                 (and (equal (fn-nsp-nb-mf r) 4) (equal (fn-nsp-nb-cf r) (+ c (- e m))))
               (and (< (fn-nsp-nb-mf r) 4) (equal (fn-nsp-nb-cf r) (+ c (len xs)))))))
  :hints (("Goal" :induct (fn-nsp-nb-ind p s bd m c xs)
           :in-theory (e/d () (fn-nsp-nb-acc fn-nsp-nb-p2 fn-nsp-nb-s2 fn-nsp-nb-bd2 fn-nsp-nb-m2 fn-nsp-nb-c2
                               fn-nsp-pat fn-nsp-sep fn-nsp-nb-q-step)))
          ("Subgoal *1/2" :cases ((equal m 0) (equal m 1) (equal m 2) (equal m 3) (equal m 4))
           :in-theory (e/d (fn-nsp-pat fn-nsp-sep fn-nsp-nb-acc-m) (fn-nsp-nb-acc)))
          ("Subgoal *1/1" :use ((:instance fn-nsp-nb-q-step
                                 (mfv (fn-nsp-nb-mf (fn-nsp-frame-block-list
                                                     (fn-nsp-nb-acc (fn-nsp-nb-p2 p (car xs)) (fn-nsp-nb-s2 p s (car xs))
                                                                    (fn-nsp-nb-bd2 p bd (car xs)) (fn-nsp-nb-m2 m (car xs))
                                                                    (fn-nsp-nb-c2 m c)) (cdr xs))))
                                 (cfv (fn-nsp-nb-cf (fn-nsp-frame-block-list
                                                     (fn-nsp-nb-acc (fn-nsp-nb-p2 p (car xs)) (fn-nsp-nb-s2 p s (car xs))
                                                                    (fn-nsp-nb-bd2 p bd (car xs)) (fn-nsp-nb-m2 m (car xs))
                                                                    (fn-nsp-nb-c2 m c)) (cdr xs))))))
           :in-theory (e/d () (fn-nsp-nb-acc fn-nsp-nb-p2 fn-nsp-nb-s2 fn-nsp-nb-bd2 fn-nsp-nb-m2 fn-nsp-nb-c2
                               fn-nsp-pat fn-nsp-sep))))))
; ---- k3f.lsp
(local (defun fn-nsp-bstart (xs)
  (and (consp xs) (consp (cdr xs)) (consp (cddr xs)) (consp (cdddr xs))
       (equal (car xs) 13) (equal (cadr xs) 10) (equal (caddr xs) 13) (equal (cadddr xs) 10))))
(local (defthm fn-nsp-sep-start
  (implies (fn-nsp-bstart xs) (equal (fn-nsp-sep xs) 4))
  :hints (("Goal" :in-theory (enable fn-nsp-sep fn-nsp-bstart)))))
(local (defthm fn-nsp-sep-next
  (implies (and (consp xs) (not (fn-nsp-bstart xs)))
           (equal (fn-nsp-sep xs) (let ((r (fn-nsp-sep (cdr xs)))) (and r (+ 1 r)))))
  :hints (("Goal" :in-theory (enable fn-nsp-sep fn-nsp-bstart)))))
(local (defthm fn-nsp-sep-atom
  (implies (not (consp xs)) (equal (fn-nsp-sep xs) nil))
  :hints (("Goal" :in-theory (enable fn-nsp-sep)))))
(local (defthm fn-nsp-aux-start
  (implies (fn-nsp-bstart xs)
           (equal (fn-nntp-split-article-aux xs pr)
                  (list :ok (reverse (append '(10 13) pr)) (cdr (cdr (cdr (cdr xs)))))))
  :hints (("Goal" :in-theory (enable fn-nntp-split-article-aux fn-nsp-bstart)))))
(local (defthm fn-nsp-aux-next
  (implies (and (consp xs) (not (fn-nsp-bstart xs)))
           (equal (fn-nntp-split-article-aux xs pr) (fn-nntp-split-article-aux (cdr xs) (cons (car xs) pr))))
  :hints (("Goal" :in-theory (enable fn-nntp-split-article-aux fn-nsp-bstart)))))
(local (defthm fn-nsp-aux-atom
  (implies (not (consp xs)) (equal (fn-nntp-split-article-aux xs pr) (list :error)))
  :hints (("Goal" :in-theory (enable fn-nntp-split-article-aux)))))
(local (defun fn-nsp-aux-ind (xs pr)
  (if (and (consp xs) (not (fn-nsp-bstart xs)))
      (fn-nsp-aux-ind (cdr xs) (cons (car xs) pr))
    pr)))
(local (defthm fn-nsp-append-snoc
  (equal (append (append a (list x)) y) (append a (cons x y)))))
(local (defthm fn-nsp-take-cons-sep
  (implies (and (consp xs) (natp e) (<= 4 e))
           (equal (take (+ -2 1 e) xs) (cons (car xs) (take (+ -2 e) (cdr xs)))))))
(local (defthm fn-nsp-split-aux-sep
  (implies (true-listp pr)
           (equal (fn-nntp-split-article-aux xs pr)
                  (if (fn-nsp-sep xs)
                      (list :ok (append (reverse pr) (take (- (fn-nsp-sep xs) 2) xs)) (nthcdr (fn-nsp-sep xs) xs))
                    (list :error))))
  :hints (("Goal" :induct (fn-nsp-aux-ind xs pr)
           :in-theory (disable fn-nsp-sep fn-nntp-split-article-aux fn-nsp-sep-iff-blank fn-nsp-bstart))
          (and stable-under-simplificationp
               '(:in-theory (enable fn-nsp-bstart))))))
(local (defthm fn-nsp-block-next-natp
  (natp (fn-nsp-block-next acc o))
  :hints (("Goal" :in-theory (enable fn-nsp-block-next)))
  :rule-classes (:rewrite :type-prescription)))
(local (defthm fn-nsp-nb-list-natp
  (implies (natp acc) (natp (fn-nsp-frame-block-list acc xs)))
  :hints (("Goal" :in-theory (enable fn-nsp-frame-block-list)))))
(local (defthm fn-nsp-nb-decomp-kq
  (implies (and (natp q) (natp k) (< k 8) (equal r (+ k (* 8 q))))
           (and (equal (mod r 8) (+ (fn-nsp-nb-pf r) (* 2 (fn-nsp-nb-sf r)) (* 4 (fn-nsp-nb-bdf r))))
                (equal (mod (floor r 8) 8) (fn-nsp-nb-mf r))))
  :rule-classes nil
  :hints (("Goal" :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3) (equal k 4) (equal k 5) (equal k 6) (equal k 7))
           :in-theory (enable fn-nsp-nb-pf fn-nsp-nb-sf fn-nsp-nb-bdf fn-nsp-nb-mf)))))
(local (defthm fn-nsp-nb-mod-div8
  (implies (natp r) (equal r (+ (mod r 8) (* 8 (floor r 8)))))
  :rule-classes nil))
(local (defthm fn-nsp-nb-decomp
  (implies (natp r)
           (and (equal (mod r 8) (+ (fn-nsp-nb-pf r) (* 2 (fn-nsp-nb-sf r)) (* 4 (fn-nsp-nb-bdf r))))
                (equal (mod (floor r 8) 8) (fn-nsp-nb-mf r))))
  :hints (("Goal" :use ((:instance fn-nsp-nb-decomp-kq (k (mod r 8)) (q (floor r 8)))
                        fn-nsp-nb-mod-div8)))))
; ---- k3g.lsp
(local (defthm fn-nsp-nb-bit-pf-nat (implies (natp r) (natp (fn-nsp-nb-pf r)))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-pf)))))
(local (defthm fn-nsp-nb-bit-pf (implies (natp r) (<= (fn-nsp-nb-pf r) 1))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-pf))) :rule-classes :linear))
(local (defthm fn-nsp-nb-bit-sf-nat (implies (natp r) (natp (fn-nsp-nb-sf r)))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-sf)))))
(local (defthm fn-nsp-nb-bit-sf (implies (natp r) (<= (fn-nsp-nb-sf r) 1))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-sf))) :rule-classes :linear))
(local (defthm fn-nsp-nb-bit-bdf-nat (implies (natp r) (natp (fn-nsp-nb-bdf r)))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-bdf)))))
(local (defthm fn-nsp-nb-bit-bdf (implies (natp r) (<= (fn-nsp-nb-bdf r) 1))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-bdf))) :rule-classes :linear))
(local (defthm fn-nsp-bit-cases
  (implies (and (natp x) (<= x 1)) (or (equal x 0) (equal x 1)))
  :rule-classes nil))
(local (defthm fn-nsp-bits-solve
  (implies (and (natp a) (<= a 1) (natp b) (<= b 1) (natp c) (<= c 1))
           (iff (equal (+ a (* 2 b) (* 4 c)) 2)
                (and (equal a 0) (equal b 1) (equal c 0))))
  :hints (("Goal" :cases ((< 0 a) (< 0 b) (< 0 c))))))
(local (defun fn-nsp-m8 (r) (mod r 8)))
(local (defun fn-nsp-mh (r) (mod (floor r 8) 8)))
(local (in-theory (disable fn-nsp-m8 fn-nsp-mh)))
(local (defthm fn-nsp-nb-decomp-w
  (implies (natp r)
           (and (equal (fn-nsp-m8 r) (+ (fn-nsp-nb-pf r) (* 2 (fn-nsp-nb-sf r)) (* 4 (fn-nsp-nb-bdf r))))
                (equal (fn-nsp-mh r) (fn-nsp-nb-mf r))))
  :hints (("Goal" :use fn-nsp-nb-decomp :in-theory (e/d (fn-nsp-m8 fn-nsp-mh) (fn-nsp-nb-decomp))))))
(local (defthm fn-nsp-nb-framedp-w
  (iff (fn-nsp-block-framedp r) (and (equal (fn-nsp-m8 r) 2) (equal (fn-nsp-mh r) 4)))
  :hints (("Goal" :in-theory (enable fn-nsp-block-framedp fn-nsp-m8 fn-nsp-mh)))))
(local (defthm fn-nsp-nb-framedp-fields
  (implies (natp r)
           (iff (fn-nsp-block-framedp r)
                (and (equal (fn-nsp-nb-pf r) 0) (equal (fn-nsp-nb-sf r) 1) (equal (fn-nsp-nb-bdf r) 0)
                     (equal (fn-nsp-nb-mf r) 4))))
  :hints (("Goal" :use (fn-nsp-nb-decomp-w
                        (:instance fn-nsp-bits-solve (a (fn-nsp-nb-pf r)) (b (fn-nsp-nb-sf r)) (c (fn-nsp-nb-bdf r))))
           :in-theory (disable fn-nsp-nb-decomp-w fn-nsp-bits-solve fn-nsp-nb-decomp)))))
(local (defthm fn-nsp-framed-of-bytes-is
  (implies (fn-octet-listp bytes)
           (iff (fn-nntp-framed-of-bytes bytes)
                (and (fn-nntp-crlf-validp bytes t) (fn-nntp-blank-linep bytes))))
  :hints (("Goal" :use (fn-nntp-crlf-validp-is-crlf-lines-ok fn-nntp-blank-linep-is-split-okp)
           :in-theory (e/d (fn-nntp-framed-of-bytes) (fn-nntp-crlf-validp-is-crlf-lines-ok fn-nntp-blank-linep-is-split-okp
                                                      fn-nntp-crlf-lines fn-nntp-split-article fn-nntp-crlf-validp
                                                      fn-nntp-blank-linep fn-nntp-split-okp))))))
(local (defthm fn-nsp-nb-top-flags
  (implies (and (true-listp bytes) (< (len bytes) 4503599627370496))
           (iff (and (equal (fn-nsp-nb-pf (fn-nsp-frame-block-list 2 bytes)) 0)
                     (equal (fn-nsp-nb-sf (fn-nsp-frame-block-list 2 bytes)) 1)
                     (equal (fn-nsp-nb-bdf (fn-nsp-frame-block-list 2 bytes)) 0))
                (fn-nntp-crlf-validp bytes t)))
  :hints (("Goal" :use ((:instance fn-nsp-nb-flags (p 0) (s 1) (m 0) (c 0) (xs bytes)))
           :in-theory (disable fn-nsp-nb-flags fn-nsp-nb-acc)))))
(local (defthm fn-nsp-nb-top-m
  (implies (and (true-listp bytes) (< (len bytes) 4503599627370496))
           (and (iff (equal (fn-nsp-nb-mf (fn-nsp-frame-block-list 2 bytes)) 4) (fn-nsp-sep bytes))
                (implies (fn-nsp-sep bytes)
                         (equal (fn-nsp-nb-cf (fn-nsp-frame-block-list 2 bytes)) (fn-nsp-sep bytes)))))
  :hints (("Goal" :use ((:instance fn-nsp-nb-match (p 0) (s 1) (bd 0) (m 0) (c 0) (xs bytes)))
           :in-theory (e/d (fn-nsp-pat) (fn-nsp-nb-match fn-nsp-nb-acc))))))
(local (defthm fn-nsp-nb-floor-is-cf
  (equal (floor r 64) (fn-nsp-nb-cf r))
  :hints (("Goal" :in-theory (enable fn-nsp-nb-cf)))))
(local (defthm fn-nsp-nb-list-framing
  (implies (and (fn-octet-listp bytes) (< (len bytes) 4503599627370496))
           (let ((r (fn-nsp-frame-block-list 2 bytes)))
             (and (iff (fn-nsp-block-framedp r) (fn-nntp-framed-of-bytes bytes))
                  (implies (fn-nsp-block-framedp r)
                           (let ((split (fn-nntp-split-article bytes)))
                             (and (equal (fn-nntp-split-head split) (take (fn-nsp-block-head-end r) bytes))
                                  (equal (fn-nntp-split-body split)
                                         (nthcdr (+ (fn-nsp-block-head-end r) 2) bytes))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nsp-nb-framedp-fields (r (fn-nsp-frame-block-list 2 bytes)))
                 (:instance fn-nsp-nb-list-natp (acc 2) (xs bytes))
                 (:instance fn-nsp-nb-top-flags) (:instance fn-nsp-nb-top-m)
                 fn-nsp-framed-of-bytes-is)
           :in-theory (e/d (fn-nntp-split-article fn-nsp-sep-iff-blank fn-nsp-block-head-end
                            fn-nntp-split-okp fn-nntp-split-head fn-nntp-split-body fn-nsp-split-aux-sep)
                           (fn-nsp-nb-framedp-fields fn-nsp-nb-top-flags fn-nsp-nb-top-m
                            fn-nsp-nb-list-natp fn-nsp-block-framedp fn-nsp-nb-acc fn-nsp-sep fn-nntp-crlf-lines
                            fn-nntp-blank-linep fn-nntp-crlf-validp fn-nntp-split-article-aux fn-nsp-framed-of-bytes-is
                            fn-nntp-framed-of-bytes))))))
; ---- k3h.lsp
(local (defthm fn-nsp-slice-octet-listp
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= end (len fn-octets)))
           (fn-octet-listp (fn-oct-slice-list i end fn-octets)))
  :hints (("Goal" :induct (fn-oct-slice-list i end fn-octets)
           :in-theory (enable fn-oct-slice-list fn-oct-get-is-nth)))))
(local (defthm fn-nsp-slice-append
  (implies (and (natp i) (natp k) (natp end) (<= i k) (<= k end))
           (equal (append (fn-oct-slice-list i k fn-octets) (fn-oct-slice-list k end fn-octets))
                  (fn-oct-slice-list i end fn-octets)))
  :hints (("Goal" :induct (fn-oct-slice-list i k fn-octets)
           :in-theory (enable fn-oct-slice-list)))))
(local (defthm fn-nsp-take-len-append
  (implies (true-listp a) (equal (take (len a) (append a b)) a))))
(local (defthm fn-nsp-nthcdr-len-append
  (implies (true-listp a) (equal (nthcdr (len a) (append a b)) b))))
(local (defthm fn-nsp-slice-true-listp
  (true-listp (fn-oct-slice-list i end fn-octets))
  :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))
(local (defthm fn-nsp-slice-head
  (implies (and (natp i) (natp he) (natp end) (<= (+ i he) end))
           (equal (take he (fn-oct-slice-list i end fn-octets))
                  (fn-oct-slice-list i (+ i he) fn-octets)))
  :hints (("Goal" :use ((:instance fn-nsp-slice-append (k (+ i he)))
                        (:instance fn-nsp-take-len-append (a (fn-oct-slice-list i (+ i he) fn-octets))
                                   (b (fn-oct-slice-list (+ i he) end fn-octets)))
                        (:instance fn-nsp-len-of-slice (end (+ i he))))
           :in-theory (disable fn-nsp-slice-append fn-nsp-take-len-append fn-nsp-len-of-slice)))))
(local (defthm fn-nsp-slice-tail
  (implies (and (natp i) (natp he) (natp end) (<= (+ i he) end))
           (equal (nthcdr he (fn-oct-slice-list i end fn-octets))
                  (fn-oct-slice-list (+ i he) end fn-octets)))
  :hints (("Goal" :use ((:instance fn-nsp-slice-append (k (+ i he)))
                        (:instance fn-nsp-nthcdr-len-append (a (fn-oct-slice-list i (+ i he) fn-octets))
                                   (b (fn-oct-slice-list (+ i he) end fn-octets)))
                        (:instance fn-nsp-len-of-slice (end (+ i he))))
           :in-theory (disable fn-nsp-slice-append fn-nsp-nthcdr-len-append fn-nsp-len-of-slice)))))
; ---- k3i.lsp
(local (defthm fn-nsp-nb-he-bound
  (implies (and (true-listp bytes) (< (len bytes) 4503599627370496)
                (fn-nsp-block-framedp (fn-nsp-frame-block-list 2 bytes)))
           (and (<= (+ (fn-nsp-block-head-end (fn-nsp-frame-block-list 2 bytes)) 2) (len bytes))
                (natp (fn-nsp-block-head-end (fn-nsp-frame-block-list 2 bytes)))))
  :hints (("Goal" :use ((:instance fn-nsp-nb-top-m) (:instance fn-nsp-nb-framedp-fields (r (fn-nsp-frame-block-list 2 bytes)))
                        (:instance fn-nsp-nb-list-natp (acc 2) (xs bytes))
                        (:instance fn-nsp-sep-natp (xs bytes)))
           :in-theory (e/d (fn-nsp-block-head-end) (fn-nsp-nb-top-m fn-nsp-nb-framedp-fields fn-nsp-nb-list-natp fn-nsp-sep-natp
                                                    fn-nsp-block-framedp fn-nsp-nb-acc fn-nsp-sep))))))
(defthm fn-nsp-frame-block-is-the-framing
  (implies (and (fn-octets-p fn-octets) ; domain: the stobj recognizer, which every executable call satisfies
                (natp i) (natp end) (<= i end) (<= end (fn-octets-len fn-octets))
                (unsigned-byte-p 52 (- end i)))
           (let ((bytes (fn-oct-slice-list i end fn-octets))
                 (acc (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets)))
             (and (iff (fn-nsp-block-framedp acc) (fn-nntp-framed-of-bytes bytes))
                  (implies (fn-nsp-block-framedp acc)
                           (let ((split (fn-nntp-split-article bytes)))
                             (and (equal (fn-nntp-split-head split)
                                         (fn-oct-slice-list i (+ i (fn-nsp-block-head-end acc)) fn-octets))
                                  (equal (fn-nntp-split-body split)
                                         (fn-oct-slice-list (+ i (fn-nsp-block-head-end acc) 2)
                                                            end fn-octets))))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nsp-nb-list-framing (bytes (fn-oct-slice-list i end fn-octets)))
                 (:instance fn-nsp-nb-he-bound (bytes (fn-oct-slice-list i end fn-octets)))
                 (:instance fn-nsp-slice-head (he (fn-nsp-block-head-end (fn-nsp-frame-block-list 2 (fn-oct-slice-list i end fn-octets)))))
                 (:instance fn-nsp-slice-tail (he (+ 2 (fn-nsp-block-head-end (fn-nsp-frame-block-list 2 (fn-oct-slice-list i end fn-octets)))))))
           :in-theory (e/d (fn-nsp-frame-block-is-list fn-nsp-len-of-slice fn-oct-octets-p-is-octet-listp)
                           (fn-nsp-nb-list-framing fn-nsp-nb-he-bound fn-nsp-slice-head fn-nsp-slice-tail
                            fn-nsp-frame-block-list fn-nsp-block-framedp fn-nntp-framed-of-bytes fn-nntp-split-article
                            fn-nsp-block-head-end fn-oct-slice-list fn-oct-slice-list-is-take-nthcdr)))))
; ---- k4a.lsp
(local (defthm fn-nsp-crlf-lines-aux-is-spec
  (implies (and (true-listp lines) (true-listp lr))
           (equal (fn-nntp-crlf-lines-aux bytes lr lines)
                  (let ((r (fn-nntp-crlf-lines-spec bytes lr)))
                    (if (equal (car r) :ok)
                        (list :ok (revappend lines (car (cdr r))))
                      r))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-nntp-crlf-lines-aux bytes lr lines)
           :in-theory (enable fn-nntp-crlf-lines-aux)))))
(local (defthm fn-nsp-spec-shape
  (let ((r (fn-nntp-crlf-lines-spec bytes lr)))
    (or (equal r (list :error)) (equal r (list :ok (cadr r)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-nntp-crlf-lines-spec bytes lr)))))
(local (defthm fn-nsp-spec-shape-ok
  (implies (equal (car (fn-nntp-crlf-lines-spec bytes lr)) :ok)
           (equal (fn-nntp-crlf-lines-spec bytes lr) (list :ok (cadr (fn-nntp-crlf-lines-spec bytes lr)))))
  :rule-classes nil
  :hints (("Goal" :use fn-nsp-spec-shape))))
(local (defthm fn-nsp-crlf-lines-is-spec
  (implies (fn-octet-listp bytes)
           (equal (fn-nntp-crlf-lines bytes) (fn-nntp-crlf-lines-spec bytes nil)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-crlf-lines) (fn-nntp-crlf-lines-aux))
           :use ((:instance fn-nsp-crlf-lines-aux-is-spec (lr nil) (lines nil)) (:instance fn-nsp-spec-shape-ok (lr nil)))))))
(local (defthm fn-nsp-line-contentp-reverse
  (implies (fn-wire-line-contentp lr) (fn-wire-line-contentp (reverse lr)))
  :hints (("Goal" :use fn-wire-line-contentp-reverse-octets
           :in-theory (e/d (fn-wire-reverse-octets-is-revappend) (fn-wire-line-contentp-reverse-octets))))))
(local (defthm fn-nsp-spec-clean-source
  (implies (and (fn-octet-listp bytes) (fn-wire-line-contentp lr) (true-listp lr)
                (equal (car (fn-nntp-crlf-lines-spec bytes lr)) :ok))
           (and (fn-wire-clean-linesp (cadr (fn-nntp-crlf-lines-spec bytes lr)))
                (equal (fn-wire-source-lines (cadr (fn-nntp-crlf-lines-spec bytes lr)))
                       (append (reverse lr) bytes))))
  :hints (("Goal" :induct (fn-nntp-crlf-lines-spec bytes lr)
           :in-theory (e/d (fn-wire-source-lines fn-wire-clean-linesp fn-wire-append-when-true-listp
                            fn-wire-line-contentp fn-wire-octetp fn-octetp fn-octet-listp)
                           ())))))
; ---- k4b.lsp
(local (defthm fn-nsp-stuff-lines-is-render
  (implies (fn-wire-clean-linesp lines)
           (equal (fn-nntp-stuff-lines lines) (fn-wire-render-lines lines)))
  :hints (("Goal" :induct (fn-wire-clean-linesp lines)
           :in-theory (e/d (fn-nntp-stuff-lines fn-nntp-crlf fn-wire-render-lines fn-wire-clean-linesp
                            fn-wire-append-when-true-listp fn-wire-line-contentp fn-wire-stuff-line)
                           ())))))
(local (defthm fn-nsp-stuff-items-of-crlf-ok
  (implies (and (fn-octet-listp x) (equal (car (fn-nntp-crlf-lines x)) :ok))
           (equal (fn-nsp-stuff-items 0 x t)
                  (list :done 0 (append (fn-nntp-stuff-lines (cadr (fn-nntp-crlf-lines x))) '(46 13 10)))))
  :hints (("Goal" :do-not-induct t :use ((:instance fn-nsp-spec-clean-source (bytes x) (lr nil))
                        (:instance fn-nsp-stuff-items-of-lines (lines (cadr (fn-nntp-crlf-lines-spec x nil))))
                        (:instance fn-nsp-stuff-lines-is-render (lines (cadr (fn-nntp-crlf-lines-spec x nil))))
                        )
           :in-theory (e/d (fn-wire-line-contentp) (fn-nsp-spec-clean-source fn-nsp-stuff-items-of-lines fn-nsp-stuff-lines-is-render
                            fn-nntp-crlf-lines fn-nntp-crlf-lines-spec fn-nntp-stuff-lines
                            fn-wire-source-lines fn-wire-render-lines fn-wire-clean-linesp))))))
; ---- k4c.lsp
(local (defun fn-nsp-v-ind (xs sp)
  (declare (xargs :measure (acl2-count xs)))
  (cond ((fn-nsp-bstart xs) sp)
        ((and (consp xs) (equal (car xs) 13) (consp (cdr xs)) (equal (cadr xs) 10))
         (fn-nsp-v-ind (cddr xs) t))
        ((consp xs) (fn-nsp-v-ind (cdr xs) nil))
        (t sp))))
(local (defthm fn-nsp-take-peel
  (implies (and (consp xs) (natp n) (< 0 n))
           (equal (take n xs) (cons (car xs) (take (- n 1) (cdr xs)))))
  :hints (("Goal" :expand ((take n xs))))))
(local (defthm fn-nsp-sep-13-10
  (implies (and (consp xs) (not (fn-nsp-bstart xs)) (equal (car xs) 13) (equal (cadr xs) 10))
           (equal (fn-nsp-sep xs) (let ((r (fn-nsp-sep (cddr xs)))) (and r (+ 2 r)))))
  :hints (("Goal" :in-theory (enable fn-nsp-bstart)
           :use ((:instance fn-nsp-sep-next (xs xs))
                 (:instance fn-nsp-sep-next (xs (cdr xs))))))))
(local (defthm fn-nsp-sep-ge-4
  (implies (fn-nsp-sep xs) (<= 4 (fn-nsp-sep xs)))
  :hints (("Goal" :use fn-nsp-sep-natp))))
(local (defthm fn-nsp-nthcdr-nthcdr
  (implies (and (natp n) (natp m))
           (equal (nthcdr n (nthcdr m xs)) (nthcdr (+ m n) xs)))
  :hints (("Goal" :induct (nthcdr m xs) :in-theory (enable nthcdr)))))
(local (defthm fn-nsp-nthcdr-2
  (implies (natp e) (equal (nthcdr (+ 2 e) xs) (nthcdr e (cddr xs))))
  :hints (("Goal" :use ((:instance fn-nsp-nthcdr-nthcdr (n e) (m 2)))
           :in-theory (e/d (nthcdr) (fn-nsp-nthcdr-nthcdr))))))
(local (defthm fn-nsp-bstart-shape
  (implies (fn-nsp-bstart xs)
           (and (equal (take 2 xs) (list 13 10))
                (equal (nthcdr 4 xs) (cddddr xs))))
  :hints (("Goal" :in-theory (enable fn-nsp-bstart)))))
(local (defthm fn-nsp-valid-bstart
  (implies (fn-nsp-bstart xs)
           (equal (fn-nntp-crlf-validp xs sp) (fn-nntp-crlf-validp (cddddr xs) t)))
  :hints (("Goal" :in-theory (e/d (fn-nsp-bstart) (fn-nntp-crlf-validp))
           :use ((:instance fn-nsp-validp-13-cons (st sp))
                 (:instance fn-nsp-validp-13-cons (xs (cddr xs)) (st t)))))))
(local (defthm fn-nsp-valid-split
  (implies (and (fn-nntp-crlf-validp xs sp) (fn-nsp-sep xs))
           (and (fn-nntp-crlf-validp (take (- (fn-nsp-sep xs) 2) xs) sp)
                (fn-nntp-crlf-validp (nthcdr (fn-nsp-sep xs) xs) t)))
  :hints (("Goal" :induct (fn-nsp-v-ind xs sp)
           :in-theory (disable fn-nsp-sep fn-nsp-bstart fn-nntp-crlf-validp))
          ("Subgoal *1/3" :cases ((equal (car xs) 13)))
          ("Subgoal *1/2" :cases ((equal (car xs) 13)))
          ("Subgoal *1/1" :cases ((equal (car xs) 13))))))
; ---- k4d.lsp
(local (defthm fn-nsp-octet-listp-take
  (implies (and (fn-octet-listp x) (natp n) (<= n (len x))) (fn-octet-listp (take n x)))
  :hints (("Goal" :in-theory (enable fn-octet-listp take)))))
(local (defthm fn-nsp-octet-listp-nthcdr
  (implies (and (fn-octet-listp x) (natp n)) (fn-octet-listp (nthcdr n x)))
  :hints (("Goal" :in-theory (enable fn-octet-listp nthcdr)))))
(local (defthm fn-nsp-k4-list
  (implies (and (fn-octet-listp bytes) (fn-nntp-crlf-validp bytes t) (fn-nsp-sep bytes)
                (member-equal kind '(:article :head :body)))
           (let* ((split (fn-nntp-split-article bytes))
                  (section (fn-nntp-section-of-bytes bytes kind))
                  (x (cond ((eq kind :article) bytes)
                           ((eq kind :head) (fn-nntp-split-head split))
                           (t (fn-nntp-split-body split)))))
             (and (equal (car section) :ok)
                  (fn-octet-listp x)
                  (equal (fn-nsp-stuff-items 0 x t)
                         (list :done 0 (append (fn-nntp-stuff-lines (cadr section)) '(46 13 10)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nsp-valid-split (xs bytes) (sp t))
                 (:instance fn-nsp-split-aux-sep (xs bytes) (pr nil))
                 (:instance fn-nsp-sep-natp (xs bytes))
                 (:instance fn-nntp-crlf-validp-is-crlf-lines-ok)
                 (:instance fn-nntp-crlf-validp-is-crlf-lines-ok (bytes (take (+ -2 (fn-nsp-sep bytes)) bytes)))
                 (:instance fn-nntp-crlf-validp-is-crlf-lines-ok (bytes (nthcdr (fn-nsp-sep bytes) bytes))))
           :in-theory (e/d (fn-nntp-section-of-bytes fn-nntp-split-article fn-nntp-split-okp fn-nntp-split-head
                            fn-nntp-split-body fn-nsp-split-aux-sep)
                           (fn-nsp-valid-split fn-nsp-sep-natp fn-nntp-crlf-validp-is-crlf-lines-ok
                            fn-nntp-crlf-lines fn-nntp-crlf-validp fn-nsp-sep fn-nntp-split-article-aux fn-nntp-stuff-lines
                            fn-nsp-stuff-items))))
))
; ---- k4e.lsp
(defthm fn-nsp-stuff-is-the-block
  (implies (and (fn-octets-p fn-octets) ; domain: the stobj recognizer, which every executable call satisfies
                (natp i) (natp end) (<= i end) (<= end (fn-octets-len fn-octets))
                (unsigned-byte-p 52 (- end i))
                (member-equal kind '(:article :head :body))
                (fn-nsp-block-framedp (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets)))
           (let* ((bytes (fn-oct-slice-list i end fn-octets))
                  (acc (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets))
                  (section (fn-nntp-section-of-bytes bytes kind)))
             (and (equal (car section) :ok)
                  (equal (fn-nsp-stuff-items
                          0 (fn-oct-slice-list (fn-nsp-section-start kind i acc)
                                               (fn-nsp-section-end kind i end acc) fn-octets)
                          t)
                         (list :done 0 (append (fn-nntp-stuff-lines (cadr section)) '(46 13 10)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nsp-frame-block-is-the-framing)
                 (:instance fn-nsp-k4-list (bytes (fn-oct-slice-list i end fn-octets)))
                 (:instance fn-nsp-slice-octet-listp)
                 (:instance fn-nsp-framed-of-bytes-is (bytes (fn-oct-slice-list i end fn-octets)))
                 (:instance fn-nsp-len-of-slice))
           :in-theory (e/d (fn-nsp-section-start fn-nsp-section-end)
                           (fn-nsp-k4-list fn-nsp-slice-octet-listp
                            fn-nsp-framed-of-bytes-is fn-nsp-len-of-slice fn-nntp-section-of-bytes
                            fn-nntp-split-article fn-nntp-framed-of-bytes fn-oct-slice-list
                            fn-oct-slice-list-is-take-nthcdr fn-nsp-block-head-end fn-nsp-block-framedp
                            fn-nntp-stuff-lines fn-nsp-stuff-items fn-nntp-crlf-validp)))))
; ---- k5.lsp
(local (defthm fn-nsp-stuff-is-the-block-rw
  (implies (and (fn-octets-p fn-octets)
                (natp i) (natp end) (<= i end) (<= end (fn-octets-len fn-octets))
                (unsigned-byte-p 52 (- end i))
                (member-equal kind '(:article :head :body))
                (fn-nsp-block-framedp (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets)))
           (equal (fn-nsp-stuff-items
                   0 (fn-oct-slice-list (fn-nsp-section-start kind i (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets))
                                        (fn-nsp-section-end kind i end (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets))
                                        fn-octets)
                   t)
                  (list :done 0 (append (fn-nntp-stuff-lines (cadr (fn-nntp-section-of-bytes (fn-oct-slice-list i end fn-octets) kind)))
                                        '(46 13 10)))))
  :hints (("Goal" :use fn-nsp-stuff-is-the-block))))
(defthm fn-nsp-response-block-host-run-is-the-block
  (implies (and (fn-octets-p fn-octets) ; domain: the stobj recognizer, which every executable call satisfies
                (natp i) (natp end) (<= i end) (<= end (fn-octets-len fn-octets))
                (unsigned-byte-p 52 (- end i))
                (member-equal kind '(:article :head :body))
                (fn-nsp-block-framedp (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets))
                (<= (fn-dss-calls-bound (list (fn-oct-slice-list
                                               (fn-nsp-section-start kind i (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets))
                                               (fn-nsp-section-end kind i end (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets))
                                               fn-octets)))
                    (nfix fuel))
                (fn-dss-a-host-room 3 rooms fuel))
           (let* ((acc (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets))
                  (section (fn-nntp-section-of-bytes (fn-oct-slice-list i end fn-octets) kind))
                  (run (fn-nsp-stuff-host-run
                        0 (list (fn-oct-slice-list (fn-nsp-section-start kind i acc)
                                                   (fn-nsp-section-end kind i end acc) fn-octets))
                        t rooms fuel buf fn-dss-out)))
             (equal (list (mv-nth 0 run) (mv-nth 1 run) (mv-nth 2 run))
                    (list :done 0 (append (fn-nntp-stuff-lines (cadr section)) '(46 13 10))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (                 (:instance fn-nsp-stuff-drive-stobj-is-items
                            (s 0) (last t) (fn-octets buf)
                            (pieces (list (fn-oct-slice-list (fn-nsp-section-start kind i (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets))
                                                             (fn-nsp-section-end kind i end (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets))
                                                             fn-octets)))))
           :in-theory (e/d (fn-dss-flatten true-list-listp)
                           (fn-nsp-stuff-drive-stobj-is-items fn-nsp-stuff-host-run
                            fn-oct-slice-list fn-oct-slice-list-is-take-nthcdr fn-dss-calls-bound fn-dss-a-host-room
                            fn-nsp-section-start fn-nsp-section-end fn-nntp-section-of-bytes fn-nsp-stuff-items fn-nsp-frame-block-is-list
                            fn-nntp-stuff-lines)))))
; ---- k9.lsp
(defthm fn-nsp-article-response-of-span
  (implies (and (fn-octets-p fn-octets) ; domain: the stobj recognizer, which every executable call satisfies
                (natp i) (natp end) (<= i end) (<= end (fn-octets-len fn-octets))
                (unsigned-byte-p 52 (- end i))
                (member-equal kind '(:article :head :body))
                (fn-nntp-article-idp article)
                (not (fn-rcl-tombstonep (fn-oct-slice-list i end fn-octets))))
           (let* ((bytes (fn-oct-slice-list i end fn-octets))
                  (acc (fn-nsp-frame-block *fn-nsp-block-init* i end fn-octets))
                  (reply (fn-nntp-article-response-of-bytes session article bytes number kind updatep group)))
             (if (fn-nsp-block-framedp acc)
                 (mv-let (r s2 items)
                   (fn-nsp-stuff-items 0 (fn-oct-slice-list (fn-nsp-section-start kind i acc)
                                                            (fn-nsp-section-end kind i end acc) fn-octets)
                                       t)
                   (declare (ignore s2))
                   (and (equal r :done)
                        (equal reply
                               (fn-nntp-make-result
                                (if updatep (fn-nntp-set-cursor session group number) session)
                                (list (fn-nntp-reply-effect
                                       (append (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))
                                               items)))))))
               (equal reply (fn-nntp-single session "503 stored article framing unavailable")))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nsp-frame-block-is-the-framing)
                 (:instance fn-nsp-stuff-is-the-block))
           :in-theory (e/d (fn-nntp-article-response-of-bytes)
                           (fn-nsp-section-start fn-nsp-section-end fn-nsp-frame-block-is-list fn-nsp-stuff-is-the-block-rw
                            fn-oct-slice-list fn-oct-slice-list-is-take-nthcdr fn-nsp-block-framedp fn-nsp-stuff-items
                            fn-nntp-section-of-bytes fn-nntp-framed-of-bytes fn-nntp-stuff-lines fn-nntp-retrieval-initial
                            fn-nntp-crlf fn-nntp-single fn-nntp-make-result fn-nntp-set-cursor fn-nntp-reply-effect)))))
; ---- k1a.lsp
(local (defun fn-nsp-ws-of (out crp ll bl)
  (fn-wire-make-state :command (reverse out) (len out) nil crp 0 ll bl)))
(local (defthm fn-nsp-feed-ws
  (implies (and (true-listp out) (fn-octetp o) (natp ll) (< 0 ll) (natp bl) (<= (len out) ll)
                (or (equal crp t) (null crp)))
           (equal (fn-wire-feed-byte (fn-nsp-ws-of out crp ll bl) o)
                  (cond (crp (if (eql o 10)
                                 (fn-wire-make-result (fn-wire-make-state :command nil 0 nil nil 0 ll bl)
                                                      (list (fn-wire-command-event out)))
                               (fn-wire-make-result (fn-wire-make-state :closed nil 0 nil nil 0 ll bl)
                                                    (list (fn-wire-reject-event :malformed)))))
                        ((eql o 13) (fn-wire-make-result (fn-nsp-ws-of out t ll bl) nil))
                        ((eql o 10) (fn-wire-make-result (fn-wire-make-state :closed nil 0 nil nil 0 ll bl)
                                                         (list (fn-wire-reject-event :malformed))))
                        ((< (len out) ll) (fn-wire-make-result (fn-nsp-ws-of (append out (list o)) nil ll bl) nil))
                        (t (fn-wire-make-result (fn-wire-make-state :closed nil 0 nil nil 0 ll bl)
                                                (list (fn-wire-reject-event :line-overlimit)))))))
  :hints (("Goal" :in-theory (e/d (fn-wire-feed-byte fn-wire-after-line fn-wire-close fn-nsp-ws-of fn-octetp
                                   fn-wire-octetp fn-wire-take-octet fn-wire-reverse-octets-is-revappend)
                                  ())))))
; ---- k1b.lsp
(local (defun fn-nsp-fenc (n cr) (+ (* 2 n) (if cr 1 0))))
(local (defthm fn-nsp-frame-step-enc
  (implies (and (natp n) (natp ll) (<= n ll) (< ll 36028797018963968) (natp o) (or (equal cr t) (null cr)))
           (equal (fn-nsp-frame-step ll (fn-nsp-fenc n cr) o)
                  (cond (cr (if (eql o 10) (list 0 0 0 1) (list *fn-nsp-refused-malformed* 0 0 2)))
                        ((eql o 13) (list (fn-nsp-fenc n t) 0 0 0))
                        ((eql o 10) (list *fn-nsp-refused-malformed* 0 0 2))
                        ((< n ll) (list (fn-nsp-fenc (+ n 1) nil) 1 o 0))
                        (t (list *fn-nsp-refused-overlimit* 0 0 2)))))
  :hints (("Goal" :in-theory (e/d (fn-nsp-frame-step fn-nsp-fenc) ())))))
(local (in-theory (disable fn-nsp-fenc fn-nsp-frame-step)))
; ---- k1c.lsp
(local (defun fn-nsp-sl (ws xs i)
  (declare (xargs :measure (len xs)))
  (if (consp xs)
      (let ((r (fn-wire-feed-byte ws (car xs))))
        (if (consp (fn-wire-result-events r))
            (fn-wsp-make (fn-wire-result-state r) (fn-wire-result-events r) (+ 1 i))
          (fn-nsp-sl (fn-wire-result-state r) (cdr xs) (+ 1 i))))
    (fn-wsp-make ws nil i))))
(local (defun fn-nsp-f-ind (out crp xs ll i)
  (declare (xargs :measure (len xs)))
  (if (consp xs)
      (let ((o (car xs)))
        (cond (crp nil)
              ((eql o 13) (fn-nsp-f-ind out t (cdr xs) ll (+ 1 i)))
              ((eql o 10) nil)
              ((< (len out) ll) (fn-nsp-f-ind (append out (list o)) nil (cdr xs) ll (+ 1 i)))
              (t nil)))
    i)))
(local (defthm fn-nsp-lstl-n-natp
  (natp (mv-nth 3 (fn-nsp-frame-list-loop ll s xs last room)))
  :hints (("Goal" :induct (fn-nsp-frame-list-loop ll s xs last room)
           :in-theory (enable fn-nsp-frame-list-loop)))
  :rule-classes (:rewrite :type-prescription)))
(local (defthm fn-nsp-lstl-step
  (implies (and (consp xs) (natp room) (<= 1 room) (natp n) (natp ll) (<= n ll) (< ll 36028797018963968)
                (fn-octetp (car xs)) (or (equal cr t) (null cr)))
           (equal (fn-nsp-frame-list-loop ll (fn-nsp-fenc n cr) xs nil room)
                  (cond (cr (if (eql (car xs) 10)
                                (list :yield 0 nil 1)
                              (list :refused *fn-nsp-refused-malformed* nil 0)))
                        ((eql (car xs) 13)
                         (let ((rec (fn-nsp-frame-list-loop ll (fn-nsp-fenc n t) (cdr xs) nil room)))
                           (list (mv-nth 0 rec) (mv-nth 1 rec) (mv-nth 2 rec) (+ 1 (mv-nth 3 rec)))))
                        ((eql (car xs) 10) (list :refused *fn-nsp-refused-malformed* nil 0))
                        ((< n ll)
                         (let ((rec (fn-nsp-frame-list-loop ll (fn-nsp-fenc (+ n 1) nil) (cdr xs) nil (- room 1))))
                           (list (mv-nth 0 rec) (mv-nth 1 rec) (cons (car xs) (mv-nth 2 rec)) (+ 1 (mv-nth 3 rec)))))
                        (t (list :refused *fn-nsp-refused-overlimit* nil 0)))))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-nsp-frame-list-loop ll (fn-nsp-fenc n cr) xs nil room))
           :in-theory (e/d (fn-oct-word-octets fn-octetp) ((:executable-counterpart fn-nsp-fenc)))))))
(local (defthm fn-nsp-lstl-atom
  (implies (not (consp xs)) (equal (fn-nsp-frame-list-loop ll s xs nil room) (list :need-input s nil 0)))
  :hints (("Goal" :expand ((fn-nsp-frame-list-loop ll s xs nil room))))))
(local (defthm fn-nsp-frame-list-open
  (implies (and (natp room) (<= 1 room))
           (equal (fn-nsp-frame-list ll s xs nil room) (fn-nsp-frame-list-loop ll s xs nil room)))
  :hints (("Goal" :in-theory (enable fn-nsp-frame-list)))))
(local (defthm fn-nsp-octet-snoc
  (implies (and (fn-octet-listp out) (fn-octetp o)) (fn-octet-listp (append out (list o))))
  :hints (("Goal" :in-theory (enable fn-octet-listp)))))
(local (defthm fn-nsp-true-snoc
  (implies (true-listp out) (true-listp (append out (list o))))))
(local (defthm fn-nsp-octet-car
  (implies (and (fn-octet-listp xs) (consp xs)) (fn-octetp (car xs)))))
(local (defthm fn-nsp-octet-cdr
  (implies (and (fn-octet-listp xs) (consp xs)) (fn-octet-listp (cdr xs)))))
(local (defthm fn-nsp-octet-natp-car
  (implies (and (fn-octet-listp xs) (consp xs)) (natp (car xs)))
  :hints (("Goal" :in-theory (enable fn-octet-listp fn-octetp)))))
(local (defthm fn-nsp-ws-of-limits
  (and (equal (fn-wire-state-line-limit (fn-nsp-ws-of out crp ll bl)) ll)
       (equal (fn-wire-state-body-limit (fn-nsp-ws-of out crp ll bl)) bl))
  :hints (("Goal" :in-theory (enable fn-nsp-ws-of)))))
(local (defthm fn-nsp-frame-wsp-need
  (implies (and (true-listp out2) (or (equal crp t) (null crp)))
           (equal (fn-nsp-frame-wsp :need-input (fn-nsp-fenc (len out2) crp) i2 out2 (fn-nsp-ws-of out0 ocrp ll bl))
                  (fn-wsp-make (fn-nsp-ws-of out2 crp ll bl) nil i2)))
  :hints (("Goal" :in-theory (e/d (fn-nsp-frame-wsp fn-nsp-ws-of fn-nsp-fenc fn-wire-reverse-octets-is-revappend)
                                  ())))))
(local (defthm fn-nsp-frame-wsp-refused
  (equal (fn-nsp-frame-wsp :refused s2 i2 out2 (fn-nsp-ws-of out0 crp0 ll bl))
         (fn-wsp-make (fn-wire-make-state :closed nil 0 nil nil 0 ll bl)
                      (list (fn-wire-reject-event (if (equal s2 *fn-nsp-refused-overlimit*) :line-overlimit :malformed)))
                      (+ 1 i2)))
  :hints (("Goal" :in-theory (enable fn-nsp-frame-wsp)))))
(local (defthm fn-nsp-frame-wsp-yield
  (equal (fn-nsp-frame-wsp :yield s2 i2 out2 (fn-nsp-ws-of out0 crp0 ll bl))
         (fn-wsp-make (fn-wire-make-state :command nil 0 nil nil 0 ll bl)
                      (list (fn-wire-command-event out2)) i2))
  :hints (("Goal" :in-theory (enable fn-nsp-frame-wsp)))))
(local (defthm fn-nsp-frame-sl
  (implies (and (true-listp out) (fn-octet-listp out) (fn-octet-listp xs) (natp ll) (< 0 ll)
                (< ll 36028797018963968) (natp bl) (<= (len out) ll)
                (or (equal crp t) (null crp)) (natp i))
           (equal (fn-nsp-sl (fn-nsp-ws-of out crp ll bl) xs i)
                  (mv-let (r s2 outs n)
                    (fn-nsp-frame-list ll (fn-nsp-fenc (len out) crp) xs nil (- (+ 1 ll) (len out)))
                    (fn-nsp-frame-wsp r s2 (+ i n) (append out outs) (fn-nsp-ws-of nil nil ll bl)))))
  :hints (("Goal" :induct (fn-nsp-f-ind out crp xs ll i)
           :in-theory (e/d (fn-nsp-sl)
                           (fn-octet-listp fn-octetp fn-nsp-ws-of fn-nsp-frame-wsp fn-wire-feed-byte fn-nsp-frame-list fn-nsp-frame-list-loop
                            (:executable-counterpart fn-nsp-fenc)))))))
; ---- k1d.lsp
(local (defthm fn-nsp-ws-rebuild-fields
  (implies (fn-wire-state-shapep x)
           (equal (fn-wire-make-state (fn-wire-state-mode x) (fn-wire-state-line-rev x) (fn-wire-state-line-len x)
                                      (fn-wire-state-body-rev x) (fn-wire-state-pending-crp x)
                                      (fn-wire-state-body-size x) (fn-wire-state-line-limit x)
                                      (fn-wire-state-body-limit x))
                  x))
  :hints (("Goal" :in-theory (enable fn-wire-state-shapep fn-wire-make-state
                                     fn-wire-state-mode fn-wire-state-line-rev
                                     fn-wire-state-line-len fn-wire-state-body-rev
                                     fn-wire-state-pending-crp fn-wire-state-body-size
                                     fn-wire-state-line-limit fn-wire-state-body-limit
                                     fn-wire-ag-car fn-wire-ag-cdr)
           :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))
                    (len (cddddr x)) (len (cdr (cddddr x)))
                    (len (cddr (cddddr x))) (len (cdddr (cddddr x)))
                    (len (cddddr (cddddr x))))))))
(local (defthm fn-nsp-reverse-octets-reverse
  (implies (true-listp x) (equal (reverse (fn-wire-reverse-octets x)) x))
  :hints (("Goal" :in-theory (enable fn-wire-reverse-octets-is-revappend)))))
(local (defthm fn-nsp-octet-listp-true
  (implies (fn-wire-octet-listp x) (true-listp x))
  :rule-classes :forward-chaining))
(local (defthm fn-nsp-len-reverse-octets
  (equal (len (fn-wire-reverse-octets x)) (len x))
  :hints (("Goal" :in-theory (enable fn-wire-reverse-octets-is-revappend)))))
(local (defthm fn-nsp-statep-shape
  (implies (fn-wire-statep x) (fn-wire-state-shapep x))
  :hints (("Goal" :in-theory (enable fn-wire-statep)))))
(local (defthm fn-nsp-ws-rebuild
  (implies (and (fn-wire-statep ws) (equal (fn-wire-state-mode ws) :command))
           (equal ws (fn-nsp-ws-of (fn-wire-reverse-octets (fn-wire-state-line-rev ws))
                                   (fn-wire-state-pending-crp ws)
                                   (fn-wire-state-line-limit ws) (fn-wire-state-body-limit ws))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-nsp-ws-rebuild-fields (x ws)) (:instance fn-nsp-statep-shape (x ws)))
           :in-theory (e/d (fn-wire-statep fn-nsp-ws-of) (fn-nsp-ws-rebuild-fields fn-nsp-statep-shape))))))
; ---- k1e.lsp
(local (defun fn-nsp-fw (r s i o ll bl)
  (fn-nsp-frame-wsp r s i o (fn-nsp-ws-of nil nil ll bl))))
(local (defthm fn-nsp-frame-wsp-ws-indep
  (equal (fn-nsp-frame-wsp r s i o ws)
         (fn-nsp-fw r s i o (fn-wire-state-line-limit ws) (fn-wire-state-body-limit ws)))
  :hints (("Goal" :in-theory (enable fn-nsp-frame-wsp fn-nsp-fw)))))
(local (in-theory (disable fn-nsp-fw)))
(local (defthm fn-nsp-state-of-enc
  (implies (and (fn-wire-statep ws) (equal (fn-wire-state-mode ws) :command))
           (equal (fn-nsp-frame-state-of ws)
                  (fn-nsp-fenc (len (fn-wire-reverse-octets (fn-wire-state-line-rev ws)))
                               (fn-wire-state-pending-crp ws))))
  :hints (("Goal" :in-theory (enable fn-nsp-frame-state-of fn-nsp-fenc fn-wire-statep)))))
(local (defthm fn-nsp-sl-frame-list-gen
  (implies (and (equal ws (fn-nsp-ws-of out crp ll bl))
                (true-listp out) (fn-octet-listp out) (fn-octet-listp xs) (natp ll) (< 0 ll)
                (< ll 36028797018963968) (natp bl) (<= (len out) ll)
                (or (equal crp t) (null crp)) (natp i))
           (equal (fn-nsp-sl ws xs i)
                  (mv-let (r s2 outs n)
                    (fn-nsp-frame-list ll (fn-nsp-fenc (len out) crp) xs nil (nfix (- (+ 1 ll) (len out))))
                    (fn-nsp-frame-wsp r s2 (+ i n) (append out outs) ws))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-nsp-frame-sl))
           :in-theory (e/d (fn-nsp-frame-wsp-ws-indep fn-nsp-ws-of-limits)
                           (fn-nsp-frame-sl fn-nsp-sl fn-nsp-frame-list fn-nsp-ws-of fn-nsp-frame-wsp fn-nsp-fenc))))))
(local (defthm fn-nsp-wire-octet-listp-is
  (equal (fn-wire-octet-listp x) (fn-octet-listp x))
  :hints (("Goal" :in-theory (enable fn-wire-octet-listp fn-wire-octetp fn-octet-listp fn-octetp)))))
(local (defthm fn-nsp-reverse-octets-octet-listp
  (implies (fn-wire-octet-listp x) (fn-octet-listp (fn-wire-reverse-octets x)))
  :hints (("Goal" :use fn-wire-reverse-octets-preserves-octet-listp
           :in-theory (e/d (fn-wire-reverse-octets-is-revappend) (fn-wire-reverse-octets-preserves-octet-listp))))))
(local (defthm fn-nsp-octet-listp-rev
  (implies (fn-octet-listp x) (fn-octet-listp (rev x)))
  :hints (("Goal" :in-theory (enable fn-octet-listp rev)))))
(local (defthm fn-nsp-octet-listp-reverse
  (implies (fn-octet-listp x) (fn-octet-listp (reverse x)))
  :hints (("Goal" :in-theory (enable fn-octet-listp reverse)))))
(local (defthm fn-nsp-statep-facts
  (implies (and (fn-wire-statep ws) (equal (fn-wire-state-mode ws) :command))
           (and (fn-octet-listp (fn-wire-state-line-rev ws))
                (equal (fn-wire-state-line-len ws) (len (fn-wire-state-line-rev ws)))
                (<= (fn-wire-state-line-len ws) (fn-wire-state-line-limit ws))
                (posp (fn-wire-state-line-limit ws))
                (natp (fn-wire-state-body-limit ws))
                (or (equal (fn-wire-state-pending-crp ws) t) (null (fn-wire-state-pending-crp ws)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-wire-statep fn-nsp-wire-octet-listp-is)))))
(local (defthm fn-nsp-sl-frame-list
  (implies (and (fn-wire-statep ws) (equal (fn-wire-state-mode ws) :command)
                (< (fn-wire-state-line-limit ws) 36028797018963968)
                (fn-octet-listp xs) (natp i))
           (equal (fn-nsp-sl ws xs i)
                  (mv-let (r s2 outs n)
                    (fn-nsp-frame-list (fn-wire-state-line-limit ws) (fn-nsp-frame-state-of ws) xs nil
                                       (nfix (- (+ 1 (fn-wire-state-line-limit ws))
                                                (len (fn-wire-reverse-octets (fn-wire-state-line-rev ws))))))
                    (fn-nsp-frame-wsp r s2 (+ i n)
                                      (append (fn-wire-reverse-octets (fn-wire-state-line-rev ws)) outs) ws))))
  :hints (("Goal" :do-not-induct t :use ((:instance fn-nsp-ws-rebuild)
                        (:instance fn-nsp-sl-frame-list-gen
                                   (out (fn-wire-reverse-octets (fn-wire-state-line-rev ws)))
                                   (crp (fn-wire-state-pending-crp ws)) (ll (fn-wire-state-line-limit ws))
                                   (bl (fn-wire-state-body-limit ws)))
                        (:instance fn-nsp-state-of-enc) (:instance fn-nsp-statep-facts))
           :in-theory (e/d ()
                           (fn-nsp-state-of-enc fn-wire-statep fn-nsp-sl fn-nsp-frame-list
                            fn-nsp-ws-of fn-nsp-frame-wsp fn-nsp-frame-wsp-ws-indep fn-nsp-fenc))))))
; ---- k1f.lsp
(local (defthm fn-nsp-span-fold-is-sl
  (implies (and (natp i) (natp end) (<= i end))
           (equal (fn-wire-span-fold ws i end fn-octets)
                  (fn-nsp-sl ws (fn-oct-slice-list i end fn-octets) i)))
  :hints (("Goal" :induct (fn-wire-span-fold ws i end fn-octets)
           :in-theory (e/d (fn-wire-span-fold fn-nsp-sl fn-oct-slice-list fn-oct-get-is-nth)
                           (fn-oct-slice-list-is-take-nthcdr))))))
(defthm fn-nsp-frame-is-wire-span-fold
  (implies (and (fn-octets-p fn-octets) ; domain: the stobj recognizer, which every executable call satisfies
                (fn-wire-statep ws)
                (equal (fn-wire-state-mode ws) :command)
                (unsigned-byte-p 55 (fn-wire-state-line-limit ws))
                (natp i) (natp end) (<= i end) (<= end (fn-octets-len fn-octets))
                (equal fn-dss-out (fn-wire-reverse-octets (fn-wire-state-line-rev ws))))
           (mv-let (r s2 i2 out2)
             (fn-nsp-frame (fn-wire-state-line-limit ws) (fn-nsp-frame-state-of ws)
                           i end nil (+ 1 (fn-wire-state-line-limit ws)) fn-octets fn-dss-out)
             (equal (fn-nsp-frame-wsp r s2 i2 out2 ws)
                    (fn-wire-span-fold ws i end fn-octets))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nsp-frame-is-list (limit (fn-wire-state-line-limit ws)) (s (fn-nsp-frame-state-of ws))
                            (last nil) (cap (+ 1 (fn-wire-state-line-limit ws))))
                 (:instance fn-nsp-sl-frame-list (xs (fn-oct-slice-list i end fn-octets)))
                 (:instance fn-nsp-span-fold-is-sl)
                 (:instance fn-nsp-slice-octet-listp)
                 (:instance fn-nsp-statep-facts)
                 (:instance fn-nsp-frame-list-open (ll (fn-wire-state-line-limit ws)) (s (fn-nsp-frame-state-of ws))
                            (xs (fn-oct-slice-list i end fn-octets))
                            (room (nfix (- (+ 1 (fn-wire-state-line-limit ws)) (len (fn-wire-reverse-octets (fn-wire-state-line-rev ws))))))))
           :in-theory (e/d (fn-oct-octets-p-is-octet-listp)
                           (fn-nsp-sl-frame-list fn-nsp-span-fold-is-sl fn-nsp-slice-octet-listp
                            fn-nsp-frame-list-open fn-nsp-frame-list fn-nsp-frame-wsp fn-nsp-frame
                            fn-nsp-frame-state-of fn-wire-span-fold fn-oct-slice-list fn-oct-slice-list-is-take-nthcdr
                            fn-wire-statep fn-nsp-sl)))))
