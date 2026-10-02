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
(assert-event (mv-nth 0 (fn-cv-walk (cons *nct-new* *nct-arts*) *nct-arts* nil)))
(assert-event (equal (fn-cv-walk-steps (cons *nct-new* *nct-arts*) *nct-arts*) 1))
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
