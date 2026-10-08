; Actual guard-verified selector: valid inputs and reference outcomes.
(in-package "ACL2")
(include-book "../../books/article-stream")

(defconst *astq-one*
  (fn-make-article "<one@query.example>" 0 '("fn.a" "fn.other")
                   '(("fn.a" . 1) ("fn.other" . 3)) t 0))
(defconst *astq-two*
  (fn-make-article "<two@query.example>" 1 '("fn.a" "fn.other")
                   '(("fn.a" . 2) ("fn.other" . 7)) t 0))
(defconst *astq-articles* (list *astq-one* *astq-two*))

(assert-event
 (let* ((root (fn-make-state '("fn.a" "fn.other") '(("fn.a" . 3) ("fn.other" . 8))
                            *astq-articles* 0 nil nil))
        (it (fn-ast-select-state :number "fn.a" 2 *astq-articles* nil nil nil 0 :next))
        (done (fn-ast-select-step it 512)))
   (and (fn-statep root)
        (fn-ast-select-donep done)
        (equal (fn-ast-at 9 done) :selected)
        (equal (fn-ast-at 5 done) *astq-two*)
        (equal (fn-ast-at 5 done) (fn-nntp-find-group-number "fn.a" 2 *astq-articles*))
        (equal (fn-ast-select-step (fn-ast-select-step it 1) 511) done))))

(assert-event
 (let* ((it (fn-ast-select-state :current "fn.a" 2 *astq-articles* nil nil nil 0 :next))
        (done (fn-ast-select-step it 512)))
   (and (fn-ast-select-donep done)
        (equal (fn-ast-at 9 done) :selected)
        (equal (fn-ast-at 5 done) (fn-nntp-available-article "fn.a" 2 *astq-articles*)))))

(assert-event
 (let ((done (fn-ast-select-step
              (fn-ast-select-state :number "fn.a" 3 *astq-articles* nil nil nil 0 :next) 512)))
   (and (equal (fn-ast-at 9 done) :missing)
        (not (fn-nntp-find-group-number "fn.a" 3 *astq-articles*)))))

; Corrupted-state witness: malformed comparison row/phase is total under the
; executable guard, without scanning or revalidating the retained archive.
(assert-event
 (let ((done (fn-ast-select-step
              (fn-ast-select-state :number "fn.a" 1 nil nil 77 '(9 . 1) 0 :compare) 2)))
   (and (equal (fn-ast-at 9 done) :missing)
        (equal (fn-ast-at 5 done) nil))))

; Reachable Message-ID archive selection retains the first ID match, settles
; its available local number, and permits no group to report zero.
(assert-event
 (let ((start (fn-ast-select-state :msgid "fn.a" "<two@query.example>"
                                  *astq-articles* nil nil nil 0 :msgid-next)))
   (let ((done (fn-ast-select-step start 512)))
     (and (eq (fn-ast-at 9 done) :selected)
          (equal (fn-ast-at 5 done) (fn-find-article "<two@query.example>" *astq-articles*))
          (equal (fn-ast-at 3 done) (fn-nntp-article-number "fn.a" *astq-two*))
          (equal (fn-ast-at 3 (fn-ast-select-step (fn-ast-msgid-local-start nil *astq-two*) 512)) 0)))))

; Literal unconditional fuel-composition witness; changing the second budget
; actually changes this unfinished retained cursor.
(assert-event
 (let ((start (fn-ast-select-state :msgid "fn.a" "<two@query.example>"
                                  *astq-articles* nil nil nil 0 :msgid-next)))
   (and (equal (fn-ast-select-step (fn-ast-select-step start 1) 2)
               (fn-ast-select-step start (+ (nfix 1) (nfix 2))))
        (not (equal (fn-ast-select-step (fn-ast-select-step start 1) 2)
                    (fn-ast-select-step start 4))))))

(defun astq-xref-result (it fuel)
  (declare (xargs :measure (nfix fuel) :verify-guards nil))
  (mv-let (word pair next) (fn-ast-xref-one it)
    (if (or (zp fuel) (not (eq word :wait))) (list word pair next)
      (astq-xref-result next (- fuel 1)))))

; Reachable positive: the actual iterator validates the word and first
; matching membership before reporting its numbered pair.
(assert-event
 (let* ((members '(("fn.a" . 1) ("fn.other" . 3)))
        (result (astq-xref-result (fn-ast-xref-state members members :next nil 0 nil 0) 512))
        (pair (cadr result)))
   (and (eq (car result) :pair)
        (consp pair) (stringp (car pair)) (< 0 (length (car pair)))
        (integerp (cdr pair)) (< 0 (cdr pair))
        (<= (cdr pair) *fn-nntp-max-article-number*)
        (equal pair '("fn.a" . 1)))))

; Remove the disposition hypothesis: the guard is T, and an actual exhausted
; iterator reports END with no pair, falsifying the numbered-pair conclusion.
(assert-event
 (mv-let (word pair next) (fn-ast-xref-one (fn-ast-xref-state nil nil :next nil 0 nil 0))
   (declare (ignore next))
   (and (eq word :end) (not (eq word :pair)) (not (consp pair)))))

; Separate corrupted retained-state totality witnesses, no array or string
; access is attempted using a malformed word/pair or lookup row.
(assert-event
 (and (equal (car (astq-xref-result
                       (fn-ast-xref-state 77 nil :word 9 0 nil 0) 0)) :wait)
      (equal (car (astq-xref-result
                       (fn-ast-xref-state nil nil :compare '("fn.a" . 1) 0 77 0) 0)) :wait)
      (equal (car (astq-xref-result
                       (fn-ast-xref-state nil nil :compare '("fn.a" . 0) 0
                                          '(("fn.a" . 0)) 0) 0)) :wait)))

; The render guard's cursor invariant (ARTICLE-PATH-UNVERIFIED-GUARDS): a cursor the
; owner publishes is a valid cursor and stays one at every unit of a full render;
; a cursor whose server octets or pair list are corrupt is refused by the recognizer.
(defconst *astq-lit* '(nil 0 3 (65 66 67)))
(defconst *astq-scan* (list *astq-lit* *astq-lit* nil t 0 *astq-lit* nil))

(defun astq-cursorp-all (cur n fn-arena)
  (declare (xargs :stobjs fn-arena :mode :program))
  (cond ((not (fn-ast-cursorp cur fn-arena)) nil)
        ((or (zp n) (eq (car cur) :done)) (eq (car cur) :done))
        (t (mv-let (out next) (fn-ast-render-one cur fn-arena)
             (declare (ignore out))
             (astq-cursorp-all next (- n 1) fn-arena)))))

(assert-event
 (let ((cur (fn-ast-ready-memberships *astq-scan* :article 1 *astq-one* '(110 111 100 101))))
   (and (fn-ast-cursorp cur fn-arena)
        (astq-cursorp-all cur 500 fn-arena))))

(assert-event
 (let ((cur (fn-ast-ready-memberships *astq-scan* :body 1 *astq-one* nil)))
   (astq-cursorp-all cur 500 fn-arena)))

; the window the plan carries is a window after a partial render
(assert-event
 (let ((cur (fn-ast-ready-memberships *astq-scan* :article 1 *astq-one* '(110 111 100 101))))
   (mv-let (bytes next) (fn-ast-render-window cur 5000 7 fn-arena)
     (and (equal (len bytes) 7) (fn-ast-windowp next fn-arena)
          (mv-let (bytes2 next2) (fn-ast-render-window next 5000 5000 fn-arena)
            (and (fn-ast-windowp next2 fn-arena) (fn-ast-window-donep next2)
                 (equal (nthcdr (- (len bytes2) 3) bytes2) '(46 13 10))))))))

; negatives: corrupt server octets / piece lists are not cursors
(assert-event
 (and (not (fn-ast-cursorp (list :xref-seek-first nil 0 nil nil t '(1 2 "x")) fn-arena))
      (not (fn-ast-cursorp (list :xref-seek-first nil 0 nil nil t '(256)) fn-arena))
      (not (fn-ast-cursorp (list :xref nil 0 '(5) nil t nil) fn-arena))
      (not (fn-ast-cursorp (list :payload '(7) 0 nil nil t nil) fn-arena))
      (not (fn-ast-cursorp (list :xref-server nil 0 nil nil t (list :xref-server '(1) 2)) fn-arena))
      (fn-ast-cursorp (list :xref-server nil 0 nil nil t (list :xref-server '(110) '(110))) fn-arena)))

; The span renderer (ARTICLE-RENDER-WALKS-FROM-WINDOW): over an arena payload
; of 700 octets (crossing two 256-octet chunks, with dot-stuffed line starts)
; the chunked render equals the per-octet render, whole and in windows of 7;
; and fn-ast-chunk-validp has teeth: a chunk that is not the arena's span
; changes the output, and is refused by the validity test.
(defun astq-span-payload (n acc)
  (declare (xargs :mode :program))
  (if (zp n) acc
    (astq-span-payload (- n 1)
                       (cons (case (mod n 5) (0 10) (1 46) (t (+ 65 (mod n 26)))) acc))))

(defun astq-span-run (payload fn-arena)
  (declare (xargs :stobjs fn-arena :mode :program))
  (let* ((fn-arena (fn-arena-seal-list payload fn-arena))
         (cur (list :payload nil 0 nil (list 0 0 (len payload) nil) t nil))
         (bad (cons (if (equal (car payload) 7) 8 7) (cdr payload))))
    (mv-let (c1 n1) (fn-ast-render-window-aux-chunk cur nil nil 5000 5000 nil fn-arena)
      (mv-let (o1 m1) (fn-ast-render-window-aux cur nil 5000 5000 nil fn-arena)
        (mv-let (c2 n2) (fn-ast-render-window-aux-chunk cur nil nil 5000 7 nil fn-arena)
          (mv-let (o2 m2) (fn-ast-render-window-aux cur nil 5000 7 nil fn-arena)
            (mv-let (cb nb) (fn-ast-render-window-aux-chunk cur nil bad 5000 5000 nil fn-arena)
              (declare (ignore nb))
              (mv (list (and (equal c1 o1) (equal n1 m1))
                        (and (equal c2 o2) (equal n2 m2))
                        (> (len o1) 700)
                        (fn-ast-chunk-validp cur (fn-arena-get-span 0 0 300 fn-arena) fn-arena)
                        (not (fn-ast-chunk-validp cur bad fn-arena))
                        (not (equal cb o1)))
                  fn-arena))))))))

(defun astq-span-check (payload)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena) (astq-span-run payload fn-arena) r)))

(assert-event (equal (astq-span-check (astq-span-payload 700 nil)) '(t t t t t t)))
