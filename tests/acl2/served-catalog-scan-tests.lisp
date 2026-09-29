; fn: teeth for the catalog chain's span scan (books/served-catalog-chain.lisp
; fn-scr-scan-span; PKT-479 on the served path after the catalog slice).
;
; What this book is evidence FOR.  The host's served read is
; host/owner-host.lisp fn-owner-chunk-span -> fn-scr-ocfg-read-span -> ... ->
; fn-scr-step-span-core, whose fold is (mbe :logic fn-scr-feed-span :exec
; fn-scr-scan-span): the byte fold is the logic every theorem above the read
; is stated over, and the event-at-a-time scan is what runs.  KEYSTONE
; fn-scr-scan-span-is-feed-span has no hypothesis, so there is nothing to
; remove and no must-fail; the witnesses run the executable scan on a live
; local buffer, arena and catalog, the way the host runs it, against the byte
; fold, over every sub-range of a command stream (every place a socket read
; could start and stop) and every read cut of a stream with two pipelined
; POSTs, and state the PKT-600 yield the host re-enters after.  The wire
; scan's own every-sub-range teeth are tests/acl2/served-scan-tests.lisp's.

(in-package "ACL2")
(include-book "../../books/served-catalog-chain")
(include-book "../../books/codec-attach")

; -----------------------------------------------------------------------------
; The host runs compiled code: every function it reaches is guard-verified.

(assert-event
 (equal (list (symbol-class 'fn-scr-scan-span (w state))
              (symbol-class 'fn-scr-feed-span (w state))
              (symbol-class 'fn-scr-step-span-core (w state))
              (symbol-class 'fn-scr-step-span-fast (w state)))
        (make-list 4 :initial-element :common-lisp-compliant)))

(defun scst-o (s) (fn-nntp-string-octets s))
(defun scst-line (s) (append (scst-o s) '(13 10)))

; A posting reader (the fixture of tests/acl2/served-scan-tests.lisp).
(defconst *scst-groups* '("fn.letters" "fn.test"))
(defconst *scst-config*
  (fn-inj-make-config t (scst-o "fn.example.invalid")
                      (list (scst-o "fn.letters") (scst-o "fn.test")) 32768))
(defconst *scst-observation* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *scst-reader*
  (fn-served-result-conn
   (fn-served-open (fn-initial-state *scst-groups*) 510 8192
                   *scst-config* *scst-observation* *scst-observation*
                   (fn-auth-open-config))))
(assert-event (fn-served-connp *scst-reader*))
(assert-event (fn-wire-fast-statep (fn-served-conn-wire *scst-reader*)))

(defun scst-article (subject)
  (append (scst-line "From: poster@example.invalid")
          (scst-line (concatenate 'string "Subject: " subject))
          (scst-line "Newsgroups: fn.letters")
          (scst-line "")
          (scst-line "..dot-stuffed")
          (scst-line ".")))
(defconst *scst-post-a* (append (scst-line "POST") (scst-article "a")))
(defconst *scst-two-posts*
  (append (scst-line "DATE") *scst-post-a* (scst-line "POST") (scst-article "b")))
; Retrieval commands reach the catalog arms (fn-scr-auth-step's -cat
; dispatch); a CR without LF and a bare LF are refused by the wire.
(defconst *scst-commands*
  (append (scst-line "GROUP fn.test") (scst-line "ARTICLE 1") (scst-line "OVER")
          '(65 13 66 13 10 67 10)))

; -----------------------------------------------------------------------------
; The scan against the byte fold on [i, end), and against the carried chain's
; scan (fn-scar-scan-span: the same stream over the pinned archive).

(defun scst-agree (conn i end fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :verify-guards nil))
  (let ((scan (fn-scr-scan-span conn i end nil nil nil nil fn-octets fn-arena fn-cat)))
    (and (equal scan (fn-scr-feed-span conn i end nil nil nil nil fn-octets fn-arena fn-cat))
         (equal scan (fn-scar-scan-span conn i end nil nil nil fn-octets fn-arena)))))

(defun scst-ranges-end (conn i end n fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (1+ n) end))))
  (if (or (not (natp end)) (not (natp n)) (> end n))
      t
    (and (scst-agree conn i end fn-octets fn-arena fn-cat)
         (scst-ranges-end conn i (1+ end) n fn-octets fn-arena fn-cat))))

; Every sub-range [i, end) of [0, n].
(defun scst-ranges (conn i n fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (1+ n) i))))
  (if (or (not (natp i)) (not (natp n)) (> i n))
      t
    (and (scst-ranges-end conn i i n fn-octets fn-arena fn-cat)
         (scst-ranges conn (1+ i) n fn-octets fn-arena fn-cat))))

; Every read cut: each start with the read running to n, and each end with
; the read starting at 0.
(defun scst-cuts (conn cut n fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :verify-guards nil
                  :measure (nfix (- (1+ n) cut))))
  (if (or (not (natp cut)) (not (natp n)) (> cut n))
      t
    (and (scst-agree conn 0 cut fn-octets fn-arena fn-cat)
         (scst-agree conn cut n fn-octets fn-arena fn-cat)
         (scst-cuts conn (1+ cut) n fn-octets fn-arena fn-cat))))

(defun scst-run (mode conn octets fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-octets (fn-octets-from-list octets fn-octets))
         (n (fn-octets-len fn-octets)))
    (mv (case mode
          (:ranges (scst-ranges conn 0 n fn-octets fn-arena fn-cat))
          (:cuts (scst-cuts conn 0 n fn-octets fn-arena fn-cat))
          (:scan (fn-scr-scan-span conn 0 n nil nil nil nil fn-octets fn-arena fn-cat))
          (otherwise (fn-scr-step-span-fast conn 0 n nil nil nil nil fn-octets fn-arena fn-cat)))
        fn-octets)))

(defun scst (mode conn octets)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (v fn-octets)
      (with-local-stobj fn-arena
        (mv-let (v fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (v fn-octets fn-cat)
              (mv-let (v fn-octets) (scst-run mode conn octets fn-octets fn-arena fn-cat)
                (mv v fn-octets fn-cat))
              (mv v fn-octets fn-arena)))
          (mv v fn-octets)))
      v)))

; Every sub-range of the command stream; every read cut of the POST stream.
(assert-event (scst :ranges *scst-reader* *scst-commands*))
(assert-event (scst :cuts *scst-reader* *scst-two-posts*))
(assert-event (scst :cuts *scst-reader* *scst-commands*))

; Reachable positive witnesses.
; The PKT-600 yield: DATE, then POST and its article are consumed, exactly
; one submission is carried, and the host-called entry (the mbe runs the
; scan) answers what the scan answers.
(assert-event
 (let ((r (scst :scan *scst-reader* *scst-two-posts*)))
   (and (equal (fn-served-counted-consumed r)
               (+ (len (scst-line "DATE")) (len *scst-post-a*)))
        (equal (len (fn-served-submissions
                     (fn-served-result-effects (fn-served-counted-result r))))
               1))))
(assert-event
 (equal (fn-served-counted-consumed (scst :fast *scst-reader* *scst-two-posts*))
        (+ (len (scst-line "DATE")) (len *scst-post-a*))))
; The command stream through the catalog arms: GROUP answers 211 (an empty
; group), ARTICLE 1 answers 423 and OVER 420 over the empty catalog, and the
; CR not followed by LF is refused (501) at the octet after it (35 of 39),
; where the wire closes and the read stops.
(defun scst-codes (effects)
  (if (consp effects)
      (cons (take 3 (cadr (car effects))) (scst-codes (cdr effects)))
    nil))
(assert-event
 (let ((r (scst :scan *scst-reader* *scst-commands*)))
   (and (equal (fn-served-counted-consumed r) 35)
        (equal (len *scst-commands*) 39)
        (equal (scst-codes (fn-served-result-effects (fn-served-counted-result r)))
               (list (scst-o "211") (scst-o "423") (scst-o "420") (scst-o "501")))
        (equal (fn-wire-state-mode
                (fn-served-conn-wire (fn-served-result-conn (fn-served-counted-result r))))
               :closed))))
