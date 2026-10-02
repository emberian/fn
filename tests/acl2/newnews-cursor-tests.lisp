; Teeth for books/newnews-cursor.lisp (lane served-incremental-4): NEWNEWS
; through the carried stamp index, in quanta.  Articles are the acceptance
; record (fn-make-article) available in group "g"; stamps straddle the
; threshold and one is not natural (it takes the next newer stamp).
(in-package "ACL2")
(include-book "../../books/newnews-cursor")

(defun nct-arts (i n acc)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (zp (- (nfix n) (nfix i))) acc
    (nct-arts (1+ (nfix i)) n
              (cons (fn-make-article (concatenate 'string "<a" (coerce (explode-atom i 10) 'string) "@x>")
                                     nil '("g") (list (cons "g" (1+ (nfix i)))) t
                                     (if (equal i 7) :none (+ 86390 (nfix i))))
                    acc))))
(defconst *nct-arts* (nct-arts 0 20 nil))
(defconst *nct-g* '("g"))
(defconst *nct-th* (* 1000 86400))      ; 2000-01-02 00:00:00 in DTN ms
(defconst *nct-c* (fn-nnw-refresh nil *nct-arts*))
(defmacro nct-scan () '(fn-nntp-newnews-scan *nct-g* *nct-th* *nct-arts* :none fn-arena))
(assert-event (equal (len (nct-scan)) 10))

; -----------------------------------------------------------------------------
; fn-nnw-carryp-of-refresh.  Positive: nil, then the built carry, then a
; delta refresh (one article consed on: the walk found the carried list).
(assert-event (fn-nnw-carryp nil))
(assert-event (fn-nnw-carryp *nct-c*))
(defconst *nct-new* (fn-make-article "<new@x>" nil '("g") (list (cons "g" 21)) t 86500))
(assert-event (mv-let (found acc) (fn-nnw-collect (cons *nct-new* *nct-arts*) *nct-arts* nil)
                (declare (ignore acc)) found))
(assert-event (fn-nnw-carryp (fn-nnw-refresh *nct-c* (cons *nct-new* *nct-arts*))))
; Hypothesis removal: a carry that is not exact stays inexact on a delta.
(defconst *nct-bad* (cons *nct-arts* (make-list 20 :initial-element 0)))
(assert-event (not (fn-nnw-carryp *nct-bad*)))
(assert-event (not (fn-nnw-carryp (fn-nnw-refresh *nct-bad* (cons *nct-new* *nct-arts*)))))

; -----------------------------------------------------------------------------
; fn-nnw-run-is-newnews-scan.  Positive: exact maxes (the walk stops early)
; and nil maxes (walks to the end), every quantum tried equal to the scan.
(assert-event (and (fn-nnw-maxes-okp *nct-arts* (fn-nnw-maxes *nct-arts*))
                   (equal (fn-nnw-run (fn-nnw-cursor *nct-g* *nct-th* *nct-arts*
                                                     (fn-nnw-maxes *nct-arts*) :none) 1 fn-arena)
                          (nct-scan))
                   (equal (fn-nnw-run (fn-nnw-cursor *nct-g* *nct-th* *nct-arts*
                                                     (fn-nnw-maxes *nct-arts*) :none) 3 fn-arena)
                          (nct-scan))
                   (equal (fn-nnw-run (fn-nnw-cursor *nct-g* *nct-th* *nct-arts* nil :none) 4 fn-arena)
                          (nct-scan))))
; With a natural horizon the index stops the walk before the end: the
; cursor after 12 articles is past the bound.
(defmacro nct-scan-h () '(fn-nntp-newnews-scan *nct-g* *nct-th* *nct-arts* 86450 fn-arena))
(assert-event (equal (fn-nnw-run (fn-nnw-cursor *nct-g* *nct-th* *nct-arts*
                                                (fn-nnw-maxes *nct-arts*) 86450) 2 fn-arena)
                     (nct-scan-h)))
(assert-event (mv-let (lines next)
                (fn-nnw-loop *nct-g* *nct-th* *nct-arts* (fn-nnw-maxes *nct-arts*) 86450 100 fn-arena nil)
                (and (equal lines (nct-scan-h)) (null next))))
; Hypothesis removal: maxes that understate the stamps (not okp) stop the
; walk too early and drop new articles.
(defconst *nct-low* (make-list 20 :initial-element 0))
(assert-event (and (not (fn-nnw-maxes-okp *nct-arts* *nct-low*))
                   (consp (fn-nntp-newnews-scan *nct-g* *nct-th* *nct-arts* 86000 fn-arena))
                   (not (equal (fn-nnw-run (fn-nnw-cursor *nct-g* *nct-th* *nct-arts* *nct-low* 86000)
                                           5 fn-arena)
                               (fn-nntp-newnews-scan *nct-g* *nct-th* *nct-arts* 86000 fn-arena)))))

; -----------------------------------------------------------------------------
; fn-nnw-step-residual, fn-nnw-step-lines-at-most-q, fn-nnw-step-progresses:
; one quantum of 3 from the exact cursor.
(defconst *nct-cur* (fn-nnw-cursor *nct-g* *nct-th* *nct-arts* (fn-nnw-maxes *nct-arts*) :none))
(assert-event (mv-let (lines next) (fn-nnw-step *nct-cur* 3 fn-arena)
                (and (fn-nnw-cursor-okp *nct-cur*)
                     (equal (append lines (fn-nnw-owes next fn-arena)) (fn-nnw-owes *nct-cur* fn-arena))
                     (fn-nnw-cursor-okp next)
                     (<= (len lines) 3)
                     (< (acl2-count (fn-nnw-tail next)) (acl2-count (fn-nnw-tail *nct-cur*))))))

; MUTATION witness (labelled): a stop test that ignores the horizon (uses
; the suffix maximum alone) drops the articles whose instant is the reader's
; clock.  Here the newest article has no natural stamp past the bound's own
; maximum; the mutated stop ends the reply before listing it.
(defun nct-mutant-pastp (threshold maxes)
  (and (consp maxes) (< (* 1000 (nfix (car maxes))) (rfix threshold))))
(defconst *nct-clock-arts*
  (cons (fn-make-article "<clock@x>" nil '("g") (list (cons "g" 30)) t :none)
        (nct-arts 0 3 nil)))
(assert-event (equal (len (fn-nntp-newnews-scan *nct-g* *nct-th* *nct-clock-arts* 86450 fn-arena)) 1))
(assert-event (nct-mutant-pastp *nct-th* (fn-nnw-maxes *nct-clock-arts*)))
(assert-event (not (fn-nnw-pastp *nct-th* (fn-nnw-maxes *nct-clock-arts*) 86450)))

; -----------------------------------------------------------------------------
; fn-nnw-response-is-newnews-response.  A NEWNEWS g 20000102 000000 over an
; archive holding the articles.  Positive: the carry for the archive's list;
; removal: an inexact carry for the same list answers differently.
(defconst *nct-archive* (fn-make-state *nct-g* nil *nct-arts* 0 nil nil))
(defconst *nct-args-o*
  (list (fn-nntp-string-octets "g") (fn-nntp-string-octets "20000102")
        (fn-nntp-string-octets "000000")))
(assert-event (and (fn-nnw-carryp *nct-c*)
                   (equal (fn-nnw-response nil *nct-archive* nil *nct-args-o* *nct-c* 4 fn-arena)
                          (fn-nntp-newnews-response nil *nct-archive* nil *nct-args-o* fn-arena))))
(defconst *nct-low-c* (cons *nct-arts* *nct-low*))
; A reader whose clock reads 86000 s (a natural horizon: the index may stop).
(defconst *nct-env* (fn-nntp-env (fn-clock-observation 1000 86000000 1000 t) nil nil))
(assert-event (equal (fn-nntp-newnews-reader-horizon *nct-env*) 86000))
(assert-event (equal (fn-nnw-response nil *nct-archive* *nct-env* *nct-args-o* *nct-c* 4 fn-arena)
                     (fn-nntp-newnews-response nil *nct-archive* *nct-env* *nct-args-o* fn-arena)))
(assert-event (and (not (fn-nnw-carryp *nct-low-c*))
                   (not (equal (fn-nnw-response nil *nct-archive* *nct-env* *nct-args-o* *nct-low-c* 4 fn-arena)
                               (fn-nntp-newnews-response nil *nct-archive* *nct-env* *nct-args-o* fn-arena)))))

; -----------------------------------------------------------------------------
; fn-nnw-scan-nil-past-bound (Codex r59 F2), over *nct-arts* with the reader
; clock at 86000 s.  The suffix of the articles 9..0 (stamps 86390..86399,
; article 7 without one) has smax 86399; B = 86399, 1000 B below the
; threshold 86400000.
(defconst *nct-old* (nthcdr 10 *nct-arts*))
(defconst *nct-b* 86399)
; Positive: every hypothesis holds, and the scan lists nothing.
(assert-event (and (natp 86000) (natp *nct-b*)
                   (<= (fn-nnw-smax *nct-old*) *nct-b*)
                   (<= 86000 *nct-b*)
                   (< (* 1000 *nct-b*) *nct-th*)
                   (equal (fn-nntp-newnews-scan *nct-g* *nct-th* *nct-old* 86000 fn-arena) nil)))
; Removal of (<= (fn-nnw-smax arts) b): the whole list (smax 86409); the
; other hypotheses hold, the scan lists the ten newer articles.
(assert-event (and (natp 86000) (<= 86000 *nct-b*) (< (* 1000 *nct-b*) *nct-th*)
                   (not (<= (fn-nnw-smax *nct-arts*) *nct-b*))
                   (equal (len (fn-nntp-newnews-scan *nct-g* *nct-th* *nct-arts* 86000 fn-arena))
                          10)))
; Removal of (<= horizon b): the suffix 7..0, its newest article without a
; stamp (its instant is the horizon), horizon 86500.  The smax and threshold
; hypotheses hold; the scan lists that article.
(defconst *nct-old7* (nthcdr 12 *nct-arts*))
(assert-event (and (equal (fn-article-stamp (car *nct-old7*)) :none)
                   (natp 86500) (<= (fn-nnw-smax *nct-old7*) *nct-b*) (< (* 1000 *nct-b*) *nct-th*)
                   (not (<= 86500 *nct-b*))
                   (equal (fn-nntp-newnews-scan *nct-g* *nct-th* *nct-old7* 86500 fn-arena)
                          (list (fn-nntp-string-octets "<a7@x>")))))
; Removal of (natp horizon): no reader clock (:none); the stampless article
; is listed (an instant that is not natural is new).
(assert-event (and (not (natp :none)) (<= (fn-nnw-smax *nct-old7*) *nct-b*)
                   (equal (fn-nntp-newnews-scan *nct-g* *nct-th* *nct-old7* :none fn-arena)
                          (list (fn-nntp-string-octets "<a7@x>")))))

; -----------------------------------------------------------------------------
; ARTICLES VISITED: fn-nnw-step-reads-at-most-q, fn-nnw-step-consumes-q.  A
; quantum of 3 from the start of the list without an index (it continues).
(assert-event
 (mv-let (lines next) (fn-nnw-step (fn-nnw-cursor *nct-g* *nct-th* *nct-arts* nil :none) 3 fn-arena)
   (and next
        (equal (fn-nnw-tail next) (nthcdr 3 *nct-arts*))
        (equal lines
               (car (mv-list 2 (fn-nnw-step (fn-nnw-cursor *nct-g* *nct-th* (fn-nnw-firstn 3 *nct-arts*)
                                                     nil :none)
                                      3 fn-arena))))
        (equal (len lines) 3))))
; MUTATION (labelled): an article past the first three replaced (made new
; and in the group) changes nothing in the quantum; the same replacement
; inside the prefix changes its lines.
(defconst *nct-odd* (fn-make-article "<odd@x>" nil '("g") (list (cons "g" 99)) t 99999))
(assert-event
 (and (equal (car (mv-list 2 (fn-nnw-step (fn-nnw-cursor *nct-g* *nct-th*
                                                   (append (take 3 *nct-arts*) (list *nct-odd*)
                                                           (nthcdr 4 *nct-arts*))
                                                   nil :none) 3 fn-arena)))
             (car (mv-list 2 (fn-nnw-step (fn-nnw-cursor *nct-g* *nct-th* *nct-arts* nil :none) 3 fn-arena))))
      (not (equal (car (mv-list 2 (fn-nnw-step (fn-nnw-cursor *nct-g* *nct-th*
                                                        (cons *nct-odd* (cdr *nct-arts*))
                                                        nil :none) 3 fn-arena)))
                  (car (mv-list 2 (fn-nnw-step (fn-nnw-cursor *nct-g* *nct-th* *nct-arts* nil :none)
                                         3 fn-arena)))))))

; -----------------------------------------------------------------------------
; THE PLAN CURSOR: fn-nnwp-run-is-octets at quanta 1, 3 and 64, and
; fn-nnwp-octets-of-start: the fresh plan cursor is the reference reply's
; octets (status line, stuffed scan, dot).
(defconst *nct-pc* (fn-nnwp-cursor t (fn-nnw-start *nct-g* *nct-th* *nct-arts* :none *nct-c*)))
(assert-event (fn-nnwp-cursor-okp *nct-pc*))
(assert-event (and (equal (fn-nnwp-run *nct-pc* 1 fn-arena) (fn-nnwp-octets *nct-pc* fn-arena))
                   (equal (fn-nnwp-run *nct-pc* 3 fn-arena) (fn-nnwp-octets *nct-pc* fn-arena))
                   (equal (fn-nnwp-run *nct-pc* 64 fn-arena) (fn-nnwp-octets *nct-pc* fn-arena))))
(assert-event (equal (fn-nnwp-octets *nct-pc* fn-arena)
                     (cadr (cadr (fn-nntp-multi nil (fn-proto-text "NEWNEWS" :listed) (nct-scan))))))
; Residual of one quantum: its octets, then what the next plan cursor stands
; for (no status line: it was written), are the whole reply.
(assert-event (mv-let (octets next) (fn-nnwp-step *nct-pc* 3 fn-arena)
                (and next (null (nth 1 next))
                     (equal (append octets (fn-nnwp-octets next fn-arena))
                            (fn-nnwp-octets *nct-pc* fn-arena)))))
