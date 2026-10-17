; Teeth for books/newnews-cursor.lisp (lane served-incremental-4): NEWNEWS
; through the carried stamp index, in quanta.  Articles are the acceptance
; record (fn-make-article) available in group "g"; stamps straddle the
; threshold and one is not natural (it takes the next newer stamp).
(in-package "ACL2")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")

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
(assert-event (nth 0 (mv-list 2 (fn-cv-walk (cons *nct-new* *nct-arts*) *nct-arts* nil))))
(assert-event (equal (fn-cv-walk-steps (cons *nct-new* *nct-arts*) *nct-arts*) 1))
(assert-event (fn-nnw-carryp (fn-nnw-refresh *nct-c* (cons *nct-new* *nct-arts*))))
; Hypothesis removal: a carry that is not exact stays inexact on a delta.
(defconst *nct-bad* (cons *nct-arts* (make-list 20 :initial-element 0)))
(assert-event (not (fn-nnw-carryp *nct-bad*)))
(assert-event (not (fn-nnw-carryp (fn-nnw-refresh *nct-bad* (cons *nct-new* *nct-arts*)))))
; With a natural horizon the index stops the walk before the end: the
; cursor after 12 articles is past the bound.
(defmacro nct-scan-h () '(fn-nntp-newnews-scan *nct-g* *nct-th* *nct-arts* 86450 fn-arena))

; Hypothesis removal: maxes that understate the stamps (not okp) stop the
; walk too early and drop new articles.
(defconst *nct-low* (make-list 20 :initial-element 0))
; -----------------------------------------------------------------------------
; fn-nnw-step-residual, fn-nnw-step-lines-at-most-q, fn-nnw-step-progresses:
; one quantum of 3 from the exact cursor.
(defconst *nct-cur* (fn-nnw-cursor *nct-g* *nct-th* *nct-arts* (fn-nnw-maxes *nct-arts*) :none))
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
; -----------------------------------------------------------------------------
; fn-nnw-response-is-newnews-response.  A NEWNEWS g 20000102 000000 over an
; archive holding the articles.  Positive: the carry for the archive's list;
; removal: an inexact carry for the same list answers differently.
(defconst *nct-archive* (fn-make-state *nct-g* nil *nct-arts* 0 nil nil))
(defconst *nct-args-o*
  (list (fn-nntp-string-octets "g") (fn-nntp-string-octets "20000102")
        (fn-nntp-string-octets "000000")))
(defconst *nct-low-c* (cons *nct-arts* *nct-low*))
; A reader whose clock reads 86000 s (a natural horizon: the index may stop).
(defconst *nct-env* (fn-nntp-env (fn-clock-observation 1000 86000000 1000 t) nil nil))
(assert-event (equal (fn-nntp-newnews-reader-horizon *nct-env*) 86000))

; -----------------------------------------------------------------------------
; The generated keystone's teeth (TEETH CONTRACT v1), what the declaration owes.

(defteeth fn-nnw-carryp-of-refresh
  :claim (((carried (fn-nnw-carryp carry))) (fn-nnw-carryp (fn-nnw-refresh carry arts)))
  :subject fn-nnw-refresh
  :witness ((carry *nct-c*) (arts (cons *nct-new* *nct-arts*)))
  :breaks ((carried ((carry *nct-bad*))))
  :mutations ((old-maxes (:conclusion (fn-nnw-carryp (cons arts (cdr carry))))
                         ((carry *nct-c*) (arts (cons *nct-new* *nct-arts*)))
                         :fault "a refresh that installs the new list over the old maxima")))

(defteeth-check)
