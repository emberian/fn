; fn: teeth for books/wire-scan.lisp and books/served-scan.lisp (PKT-479).
;
; What this book is evidence FOR.  The owner's served read runs
; fn-scar-scan-span (books/served-span.lisp fn-scar-step-span-core, the mbe
; executable of fn-scar-feed-span), which runs the wire machine a line at a
; time (fn-wire-scan) and dispatches once per framed event.  Both keystones
; have no hypothesis:
;   fn-wire-scan-is-span-fold: the scan IS the octet fold fn-wire-span-fold;
;   fn-scar-scan-span-is-feed-counted: the served scan IS the carried byte
;     fold fn-scar-feed-counted over the range's octets.
; With no hypothesis there is nothing to remove, so there are no must-fails;
; the witnesses run the executable scan on a live local buffer, the way the
; host runs it, against the octet folds, over every sub-range of each input
; (every place a socket read could start or stop), on command lines,
; dot-stuffed article lines, CR without LF, a bare LF, a line over the line
; limit, a body over the body limit, and two pipelined POSTs.

(in-package "ACL2")
(include-book "../../books/served-span")
(include-book "../../books/codec-attach")

; -----------------------------------------------------------------------------
; The host runs compiled code: every function it reaches is guard-verified.

(assert-event
 (equal (list (symbol-class 'fn-wire-scan (w state))
              (symbol-class 'fn-wscan-plain-end (w state))
              (symbol-class 'fn-wscan-revonto (w state))
              (symbol-class 'fn-scar-scan-span (w state))
              (symbol-class 'fn-scar-step-span-core (w state)))
        '(:common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant :common-lisp-compliant)))

(defun sct-o (s) (fn-nntp-string-octets s))
(defun sct-line (s) (append (sct-o s) '(13 10)))

; -----------------------------------------------------------------------------
; The wire scan against the octet fold, over every sub-range [i, end) of the
; buffer, from a given wire state.

(defun sct-wire-ranges-end (ws i end n fn-octets)
  (declare (xargs :stobjs fn-octets
                  :verify-guards nil
                  :measure (nfix (- (1+ n) end))))
  (if (or (not (natp end)) (not (natp n)) (> end n))
      t
    (and (equal (fn-wire-scan ws i end fn-octets)
                (fn-wire-span-fold ws i end fn-octets))
         (sct-wire-ranges-end ws i (1+ end) n fn-octets))))

(defun sct-wire-ranges (ws i n fn-octets)
  (declare (xargs :stobjs fn-octets
                  :verify-guards nil
                  :measure (nfix (- (1+ n) i))))
  (if (or (not (natp i)) (not (natp n)) (> i n))
      t
    (and (sct-wire-ranges-end ws i i n fn-octets)
         (sct-wire-ranges ws (1+ i) n fn-octets))))

(defun sct-wire-all (ws octets fn-octets)
  (declare (xargs :stobjs fn-octets
                  :verify-guards nil))
  (let ((fn-octets (fn-octets-from-list octets fn-octets)))
    (mv (sct-wire-ranges ws 0 (fn-octets-len fn-octets) fn-octets) fn-octets)))

(defun sct-wire-all-value (ws octets)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (sct-wire-all ws octets fn-octets) v)))

; The scan's result on the whole buffer, for the reachable positive witnesses.
(defun sct-wire-whole (ws octets fn-octets)
  (declare (xargs :stobjs fn-octets
                  :verify-guards nil))
  (let ((fn-octets (fn-octets-from-list octets fn-octets)))
    (mv (fn-wire-scan ws 0 (fn-octets-len fn-octets) fn-octets) fn-octets)))

(defun sct-wire-whole-value (ws octets)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (sct-wire-whole ws octets fn-octets) v)))

(defconst *sct-command* (fn-wire-initial-state 16 4096))
(defconst *sct-article*
  (fn-wire-result-state (fn-wire-begin-article (fn-wire-initial-state 16 4096))))
(defconst *sct-tight-body*
  (fn-wire-result-state (fn-wire-begin-article (fn-wire-initial-state 16 8))))
(assert-event (and (fn-wire-fast-statep *sct-command*)
                   (fn-wire-fast-statep *sct-article*)
                   (fn-wire-fast-statep *sct-tight-body*)
                   (equal (fn-wire-state-mode *sct-article*) :article)))

(defconst *sct-body* '(46 46 104 105 13 10 97 98 13 10 46 13 10 72 69 76 80 13 10))
(defconst *sct-commands* (append (sct-line "HELP") (sct-line "DATE") (sct-line "")))
(defconst *sct-cr-no-lf* '(65 66 13 67 13 10))
(defconst *sct-bare-lf* '(65 66 10 67 13 10))
(defconst *sct-long* (sct-line "ABCDEFGHIJKLMNOPQRSTUVWXYZ"))

; Every sub-range, every input, both modes (and the tight body limit).
(assert-event (sct-wire-all-value *sct-article* *sct-body*))
(assert-event (sct-wire-all-value *sct-command* *sct-commands*))
(assert-event (sct-wire-all-value *sct-command* *sct-cr-no-lf*))
(assert-event (sct-wire-all-value *sct-article* *sct-bare-lf*))
(assert-event (sct-wire-all-value *sct-command* *sct-long*))
(assert-event (sct-wire-all-value *sct-tight-body* *sct-body*))

; Reachable positive witnesses: what the scan frames, stated.
; The article: "..hi" unstuffs to ".hi", then "ab", then "." ends it, at 13.
(assert-event
 (let ((r (sct-wire-whole-value *sct-article* *sct-body*)))
   (and (equal (fn-wsp-events r)
               (list (fn-wire-article-event (list (list 46 104 105) (list 97 98)))))
        (equal (fn-wsp-next r) 13)
        (equal (fn-wire-state-mode (fn-wsp-state r)) :command))))
; A command line is one event after its LF.
(assert-event
 (let ((r (sct-wire-whole-value *sct-command* *sct-commands*)))
   (and (equal (fn-wsp-events r) (list (fn-wire-command-event (sct-o "HELP"))))
        (equal (fn-wsp-next r) 6))))
; CR not followed by LF is refused at the octet after the CR.
(assert-event
 (let ((r (sct-wire-whole-value *sct-command* *sct-cr-no-lf*)))
   (and (equal (fn-wsp-events r) (list (fn-wire-reject-event :malformed)))
        (equal (fn-wsp-next r) 4))))
; A bare LF is refused where it stands.
(assert-event
 (let ((r (sct-wire-whole-value *sct-article* *sct-bare-lf*)))
   (and (equal (fn-wsp-events r) (list (fn-wire-reject-event :malformed)))
        (equal (fn-wsp-next r) 3))))
; The line limit (16) closes at the seventeenth octet of the line, as the
; octet machine does: the run stops at the limit and the reference step
; refuses.
(assert-event
 (let ((r (sct-wire-whole-value *sct-command* *sct-long*)))
   (and (equal (fn-wsp-events r) (list (fn-wire-reject-event :line-overlimit)))
        (equal (fn-wsp-next r) 17)
        (equal (fn-wire-state-mode (fn-wsp-state r)) :closed))))
; The body limit (8) closes at the second line's LF.
(assert-event
 (let ((r (sct-wire-whole-value *sct-tight-body* *sct-body*)))
   (and (equal (fn-wsp-events r) (list (fn-wire-reject-event :body-overlimit)))
        (equal (fn-wsp-next r) 10))))
; A partial line is carried in line-rev, reversed, exactly as the octet
; machine leaves it.
(assert-event
 (let ((r (sct-wire-whole-value *sct-command* (sct-o "GRO"))))
   (and (null (fn-wsp-events r))
        (equal (fn-wsp-next r) 3)
        (equal (fn-wire-state-line-rev (fn-wsp-state r)) (list 79 82 71))
        (equal (fn-wire-state-line-len (fn-wsp-state r)) 3))))

; -----------------------------------------------------------------------------
; The served scan against the byte folds: a posting reader (the fixture of
; tests/acl2/served-pipelining-tests.lisp), two POSTs in one read.

(defconst *sct-groups* '("fn.letters" "fn.test"))
(defconst *sct-config*
  (fn-inj-make-config t (sct-o "fn.example.invalid")
                      (list (sct-o "fn.letters") (sct-o "fn.test")) 32768))
(defconst *sct-observation* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *sct-reader*
  (fn-served-result-conn
   (fn-served-open (fn-initial-state *sct-groups*) 510 8192
                   *sct-config* *sct-observation* *sct-observation*
                   (fn-auth-open-config))))
(assert-event (fn-served-connp *sct-reader*))
(assert-event (fn-wire-fast-statep (fn-served-conn-wire *sct-reader*)))

(defun sct-article (subject)
  (append (sct-line "From: poster@example.invalid")
          (sct-line (concatenate 'string "Subject: " subject))
          (sct-line "Newsgroups: fn.letters")
          (sct-line "")
          (sct-line "..dot-stuffed")
          (sct-line ".")))
(defconst *sct-post-a* (append (sct-line "POST") (sct-article "a")))
(defconst *sct-two-posts*
  (append (sct-line "DATE") *sct-post-a* (sct-line "POST") (sct-article "b")))

; The three folds on [i, end): the executable scan, the octet buffer fold and
; the carried list fold.
(defun sct-served (conn i end fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :verify-guards nil))
  (list (fn-scar-scan-span conn i end nil nil nil fn-octets fn-arena)
        (fn-scar-feed-span conn i end nil nil nil fn-octets fn-arena)
        (fn-scar-feed-counted conn (fn-oct-slice-list i end fn-octets) nil nil nil fn-arena)))

(defun sct-served-agree (conn i end fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :verify-guards nil))
  (let ((v (sct-served conn i end fn-octets fn-arena)))
    (and (equal (first v) (second v)) (equal (first v) (third v)))))

(defun sct-served-cuts (conn cut n fn-octets fn-arena)
  ; every read start 0..n with the read running to n, and every read end
  ; with the read starting at 0: the two places a socket read cuts.
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :verify-guards nil
                  :measure (nfix (- (1+ n) cut))))
  (if (or (not (natp cut)) (not (natp n)) (> cut n))
      t
    (and (sct-served-agree conn 0 cut fn-octets fn-arena)
         (sct-served-agree conn cut n fn-octets fn-arena)
         (sct-served-cuts conn (1+ cut) n fn-octets fn-arena))))

(defun sct-served-all (conn octets fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :verify-guards nil))
  (let ((fn-octets (fn-octets-from-list octets fn-octets)))
    (mv (sct-served-cuts conn 0 (fn-octets-len fn-octets) fn-octets fn-arena) fn-octets)))

(defun sct-served-all-value (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (sct-served-all conn octets fn-octets fn-arena) v)))

(defun sct-served-whole (conn octets fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :verify-guards nil))
  (let ((fn-octets (fn-octets-from-list octets fn-octets)))
    (mv (fn-scar-scan-span conn 0 (fn-octets-len fn-octets) nil nil nil fn-octets fn-arena)
        fn-octets)))

(defun sct-served-whole-value (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (v fn-octets) (sct-served-whole conn octets fn-octets fn-arena) v)))

(include-book "arena-lift")
(bpr-lift fn-served-step 2)
(bpr-lift sct-served-all-value 2)
(bpr-lift sct-served-whole-value 2)
(assert-event (in-arena-sct-served-all-value nil *sct-reader* *sct-two-posts*))

; Reachable positive witness: the read yields after the first article
; (PKT-600): DATE, then POST and its article are consumed, exactly one
; submission is carried, and it is the reference fold's.
(assert-event
 (let ((r (in-arena-sct-served-whole-value nil *sct-reader* *sct-two-posts*)))
   (and (equal (fn-served-counted-consumed r)
               (+ (len (sct-line "DATE")) (len *sct-post-a*)))
        (equal (len (fn-served-submissions
                     (fn-served-result-effects (fn-served-counted-result r))))
               1)
        (equal (fn-served-result-effects (fn-served-counted-result r))
               (fn-served-result-effects
                (in-arena-fn-served-step nil *sct-reader* (append (sct-line "DATE") *sct-post-a*)))))))
