; D2b: the NNTP grammar fuzzer (layer-D brief item 2; RELEASE-PLAN section
; 2.4, form F) and its three mutation controls.
;
; Cases are generated over the declared table (tests/grammar-gen.lisp): valid
; transcripts of pipelined command lines and dot-stuffed blocks, transcripts
; with one line or block line mutated by a named operator, and transcripts
; with random byte mutations. Every case runs through the real framer,
; parser and renderer (NAME-run-fault with no fault), unsplit and in a seeded
; chunking whose deliveries are bounded by the simulator's network capacity,
; each framer call within the 4 KiB run quantum. A valid case must parse to
; exactly the generated commands, arguments and block lines; a mutated case
; must be refused with the reply the spec table below gives; every case must
; be total, typed, stop exactly where the grammar stops, and be invariant
; under fragmentation (every split point for the first seeds). The mutation
; controls are the three deliberately wrong grammars of *fn2-gram-faults*;
; the same campaign must catch each of them.
; Run: sh fn2/tools/certify.sh tests/grammar-fuzz.lisp
(in-package "ACL2")
(include-book "../books/nntp-grammar")
(include-book "../sim/sim-state-data")
(include-book "grammar-gen")
(defgrammar-generator fn2-nntp)

; What the spec answers to each mutation, written from the spec and never
; read from the grammar: (class outcome reply closes citation). The
; outcome is the runner's code for the line; a block line's outcome is the
; block event. The H model's verdicts on the same cases are the second
; oracle (tests/grammar-fuzz-oracle.py).
(defconst *fn2-gf-spec*
  '((:nul :malformed 501 t "RFC 3977 section 3.1: no NUL in a command line; specs/nntp.md:513-518 (close)")
    (:bare-cr :malformed 501 t "RFC 3977 section 3.1: CR only as the CRLF pair")
    (:bare-lf :malformed 501 t "RFC 3977 section 3.1: a command line ends with CRLF")
    (:bad-utf8 :malformed 501 t "RFC 3977 section 3.1: UTF-8 (RFC 3629) command lines")
    (:empty :malformed 501 t "RFC 3977 section 3.1: a command line starts with its keyword")
    (:overlong :overflow 501 t "RFC 3977 sections 3.1 and 3.2.1: 512 octets with CRLF, 501 for an overlength line")
    (:control :syntax 501 nil "RFC 3977 sections 3.1 and 3.2.1: no control octet but TAB as a separator")
    (:leading-ws :syntax 501 nil "RFC 3977 section 3.1: the keyword opens the line")
    (:trailing-ws :syntax 501 nil "RFC 3977 section 3.1: separators only between words")
    (:args-overlong :syntax 501 nil "RFC 3977 section 3.1: arguments at most 497 octets")
    (:unknown :unknown 500 nil "RFC 3977 section 3.2.1; specs/nntp.md:87")
    (:extra-arg :syntax 501 nil "RFC 3977 section 3.2.1: a syntax error in the arguments")
    (:missing-arg :syntax 501 nil "RFC 3977 section 3.2.1: a syntax error in the arguments")
    (:bad-arg :syntax 501 nil "RFC 3977 sections 3.2.1, 3.6 (Message-ID), 4.2 (wildmat), 6 (number, range), 7.3 (date)")
    (:state :state (("IHAVE" . 502) ("CHECK" . 502) ("TAKETHIS" . 502) ("XFNCATCHUP" . 502) ("COMPRESS" . 480)
                    ("AUTHINFO" . 502) ("XREDEEM" . 502)) nil
            "RFC 3977 section 3.2.1 (502: not permitted on this connection); NNT-054 and layer H's ruling: COMPRESS only after authentication (480); RFC 4643 section 2.2: AUTHINFO after authentication is 502, whatever its arguments; specs/nntp.md:1784-1914 (XREDEEM likewise)")
    (:block-unstuffed :bad-line nil nil "RFC 3977 section 3.1.1: a line opening with a dot is dot-stuffed")
    (:block-nul :bad-line nil nil "RFC 3977 section 3.1.1; specs/nntp.md:2495: no NUL in a block")
    (:block-bare-cr :bad-line nil nil "RFC 3977 section 3.1.1: block lines end with CRLF")
    (:block-bare-lf :bad-line nil nil "RFC 3977 section 3.1.1: block lines end with CRLF")
    (:block-overlong :block-overflow nil nil "RFC 5322 section 2.1.1: 998 octets plus CRLF")
    (:block-no-terminator :open nil nil "RFC 3977 section 3.1.1; specs/nntp.md:513-518: body text stays body text until .CRLF")
    ;; A refused TAKETHIS line still carries its article: the server reads it and answers 439
    ;; after the terminator (the generator applies this where the keyword stands first and the
    ;; line is framed structurally).
    (:immediate :discard nil nil "RFC 4644 section 2.5.2; specs/nntp.md:530-537")))

; Reader and peer connections, anonymous, and an authenticated reader.
(defconst *fn2-gf-masks*
  (list (logior *fn2-nntp-state-reader* *fn2-nntp-state-anonymous*)
        (logior *fn2-nntp-state-peer* *fn2-nntp-state-anonymous*)
        (logior *fn2-nntp-state-reader* *fn2-nntp-state-authenticated*)))
(defconst *fn2-gf-classes*
  (append '(:valid) *fn2-gg-line-classes* *fn2-gg-block-classes* '(:random)))
; Within the fragmentation statement's premise (under 4,096 octets).
(defconst *fn2-gf-budget* 3000)

(defun fn2-gf-case (seed class mask)
  (declare (xargs :verify-guards nil))
  (if (eq class :valid) (fn2-nntp-generate seed mask *fn2-gf-budget*)
    (fn2-nntp-mutate seed class mask *fn2-gf-budget* *fn2-gf-spec*)))

; Every split point 1..n-1 gives the unsplit outcome.
(defun fn2-gf-splits (left k octets mask fault whole)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) t
    (and (equal (fn2-nntp-run-fault octets (list k) mask fault) whole)
         (fn2-gf-splits (- left 1) (+ 1 k) octets mask fault whole))))

; One case's verdict: nil (pass), :skipped (the mask has no row the class
; needs), or the name of the check that failed.
(defun fn2-gf-verdict (seed class mask fault split)
  (declare (xargs :verify-guards nil))
  (let ((case (fn2-gf-case seed class mask)))
    (if (not case) :skipped
      (let* ((octets (car case))
             (whole (fn2-nntp-run-fault octets nil mask fault))
             (sizes (mv-let (sizes rng)
                      (fn2-gg-chunks (len octets) *fn2-sim-network-capacity* (fn2-gg-rng (+ 104729 seed)))
                      (declare (ignore rng)) sizes)))
        (or (and (not (eq (nth 1 case) :unchecked)) (fn2-gg-check case whole))
            (fn2-gg-sound whole *fn2-nntp-gen-table* *fn2-nntp-command-none* (len octets))
            (and (not (equal (fn2-nntp-run-fault octets sizes mask fault) whole)) :fragmentation)
            (and split (not (fn2-gf-splits (nfix (- (len octets) 1)) 1 octets mask fault whole)) :every-split))))))

; The tally: per class (class pass fail skipped first-failure), the first
; failure as (seed mask verdict).
(defun fn2-gf-count (class verdict seed mask tally)
  (declare (xargs :verify-guards nil))
  (let* ((row (or (cdr (assoc-eq class tally)) (list 0 0 0 nil)))
         (row (cond ((null verdict) (update-nth 0 (+ 1 (nth 0 row)) row))
                    ((eq verdict :skipped) (update-nth 2 (+ 1 (nth 2 row)) row))
                    (t (update-nth 3 (or (nth 3 row) (list seed mask verdict))
                                   (update-nth 1 (+ 1 (nth 1 row)) row))))))
    (put-assoc-eq class row tally)))
(defun fn2-gf-classes (classes seed mask fault split tally)
  (declare (xargs :verify-guards nil))
  (if (atom classes) tally
    (fn2-gf-classes (cdr classes) seed mask fault split
                    (fn2-gf-count (car classes) (fn2-gf-verdict seed (car classes) mask fault split) seed mask tally))))
(defun fn2-gf-masks (masks seed fault split tally)
  (declare (xargs :verify-guards nil))
  (if (atom masks) tally
    (fn2-gf-masks (cdr masks) seed fault split (fn2-gf-classes *fn2-gf-classes* seed (car masks) fault split tally))))
; Seeds 0..N-1; every split point for seeds below SPLITS.
(defun fn2-gf-campaign (n fault splits seed tally)
  (declare (xargs :verify-guards nil :measure (nfix (- (nfix n) (nfix seed)))))
  (if (>= (nfix seed) (nfix n)) tally
    (fn2-gf-campaign n fault splits (+ 1 (nfix seed))
                     (fn2-gf-masks *fn2-gf-masks* (nfix seed) fault (< (nfix seed) (nfix splits)) tally))))

(defun fn2-gf-failures (tally)
  (declare (xargs :verify-guards nil))
  (if (atom tally) 0 (+ (nth 1 (cdar tally)) (fn2-gf-failures (cdr tally)))))
(defun fn2-gf-catchers (tally)
  (declare (xargs :verify-guards nil))
  (if (atom tally) nil
    (append (and (< 0 (nth 1 (cdar tally))) (list (caar tally))) (fn2-gf-catchers (cdr tally)))))
; Every class ran at least once (no class skipped everywhere).
(defun fn2-gf-exercised (tally)
  (declare (xargs :verify-guards nil))
  (if (atom tally) t (and (< 0 (+ (nth 0 (cdar tally)) (nth 1 (cdar tally)))) (fn2-gf-exercised (cdr tally)))))

; ------------------------------------------------------------------------
; The real grammar: 256 seeds x 3 masks x 23 classes, every split point for
; the first 4 seeds. Recorded once by MAKE-EVENT.
(make-event
 (value `(defconst *fn2-gf-real* ',(fn2-gf-campaign 256 nil 4 0 nil))))
(value-triple (cw "~%FUZZ real (class pass fail skipped first-failure):~%~x0~%" *fn2-gf-real*))
(assert-event (and (equal (fn2-gf-failures *fn2-gf-real*) 0) (fn2-gf-exercised *fn2-gf-real*)
                   (equal (len *fn2-gf-real*) (len *fn2-gf-classes*)))
              :msg (msg "The fuzz campaign failed: ~x0" *fn2-gf-real*))

; The three mutation controls: each wrong grammar is caught by the classes
; whose spec reply it violates.
(make-event
 (value `(defconst *fn2-gf-controls*
           ',(list (cons :accept (fn2-gf-catchers (fn2-gf-campaign 16 :accept 0 0 nil)))
                   (cons :reply (fn2-gf-catchers (fn2-gf-campaign 16 :reply 0 0 nil)))
                   (cons :drop (fn2-gf-catchers (fn2-gf-campaign 16 :drop 0 0 nil)))))))
(value-triple (cw "~%FUZZ controls (fault caught-by):~%~x0~%" *fn2-gf-controls*))
(assert-event (and (subsetp-eq '(:extra-arg :missing-arg :bad-arg) (cdr (assoc-eq :accept *fn2-gf-controls*)))
                   (subsetp-eq '(:control :leading-ws :trailing-ws :args-overlong :extra-arg :missing-arg :bad-arg)
                               (cdr (assoc-eq :reply *fn2-gf-controls*)))
                   (subsetp-eq '(:nul :bare-cr :bare-lf :bad-utf8 :empty) (cdr (assoc-eq :drop *fn2-gf-controls*))))
              :msg (msg "A mutation control was not caught: ~x0" *fn2-gf-controls*))
