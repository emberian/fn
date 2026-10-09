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
(defconst *astq-lit* '(nil 0 13 (72 58 32 118 13 10 13 10 65 66 67 13 10)))
(defconst *astq-scan* (list :span '(nil 13 0 nil) *astq-lit* 2 6 '(nil 8 5 (65 66 67 13 10))))

(defun astq-cursorp-all (cur n fn-arena)
  (declare (xargs :stobjs fn-arena :mode :program))
  (cond ((not (fn-ast-cursorp cur fn-arena)) nil)
        ; the payload phase is rendered by the window a quantum at a time, not by render-one
        ((or (zp n) (member-eq (car cur) '(:done :payload))) (member-eq (car cur) '(:done :payload)))
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

; the window the plan carries is a window after a partial render; the
; render runs until done, each call writing at most its window.
(defun astq-render-calls (window octets k fn-arena fn-ast-ws fn-dss-out)
  (declare (xargs :stobjs (fn-arena fn-ast-ws fn-dss-out) :mode :program))
  (if (zp k) (mv (list window nil) fn-ast-ws fn-dss-out)
    (mv-let (next fn-ast-ws fn-dss-out) (fn-ast-render-window window 5000 octets fn-arena fn-ast-ws fn-dss-out)
      (let ((bytes (fn-dss-out-list fn-dss-out)))
        (if (or (< octets (len bytes)) (not (fn-ast-windowp next fn-arena)))
            (mv (list :bad nil) fn-ast-ws fn-dss-out)
          (if (fn-ast-window-donep next) (mv (list next bytes) fn-ast-ws fn-dss-out)
            (mv-let (r fn-ast-ws fn-dss-out) (astq-render-calls next octets (- k 1) fn-arena fn-ast-ws fn-dss-out)
              (mv (list (car r) (append bytes (cadr r))) fn-ast-ws fn-dss-out))))))))

(defun astq-render (window octets fn-arena)
  (declare (xargs :stobjs fn-arena :mode :program))
  (with-local-stobj fn-ast-ws
    (mv-let (r fn-ast-ws)
      (with-local-stobj fn-dss-out
        (mv-let (r fn-ast-ws fn-dss-out) (astq-render-calls window octets 100000 fn-arena fn-ast-ws fn-dss-out)
          (mv r fn-ast-ws)))
      r)))

(assert-event
 (let* ((cur (fn-ast-ready-memberships *astq-scan* :article 1 *astq-one* '(110 111 100 101)))
        (r7 (astq-render cur 7 fn-arena)) (r1 (astq-render cur 1 fn-arena)) (rall (astq-render cur 5000 fn-arena)))
   (and (fn-ast-window-donep (car r7)) (equal (cadr r7) (cadr rall)) (equal (cadr r1) (cadr rall))
        (equal (nthcdr (- (len (cadr rall)) 3) (cadr rall)) '(46 13 10)))))

; negatives: corrupt server octets / piece lists are not cursors
(assert-event
 (and (not (fn-ast-cursorp (list :xref-seek-first nil 0 nil nil t '(1 2 "x")) fn-arena))
      (not (fn-ast-cursorp (list :xref-seek-first nil 0 nil nil t '(256)) fn-arena))
      (not (fn-ast-cursorp (list :xref nil 0 '(5) nil t nil) fn-arena))
      (not (fn-ast-cursorp (list :payload '(7) 0 nil nil t nil) fn-arena))
      (not (fn-ast-cursorp (list :xref-server nil 0 nil nil t (list :xref-server '(1) 2)) fn-arena))
      (fn-ast-cursorp (list :xref-server nil 0 nil nil t (list :xref-server '(110) '(110))) fn-arena)))

;; The span path over a literal payload of 700 octets (dot-stuffed line
;; starts; a handle payload reads through A-ARENA-SPAN-INTO, which only the
;; host executes: tests/native_article_stream_source.lisp): the windowed
;; preflight finds the same head end in quanta of 1, 7 and 5000 and the
;; windowed render of the payload phase is fn-nsp-stuff's one-pass stream
;; for windows of 1, 2, 7 and 5000.
(defun astq-span-payload (n acc)
  (declare (xargs :mode :program))
  (if (zp n) acc
    (astq-span-payload (- n 1)
                       (cons (case (mod n 5) (0 10) (4 13) (1 46) (t (+ 65 (mod n 26)))) acc))))

(defun astq-scan-all (scan fuel k fn-arena fn-ast-ws)
  (declare (xargs :stobjs (fn-arena fn-ast-ws) :mode :program))
  (if (or (zp k) (fn-ast-scan-donep scan)) (mv scan fn-ast-ws)
    (mv-let (scan fn-ast-ws) (fn-ast-scan-step scan fuel fn-arena fn-ast-ws)
      (astq-scan-all scan fuel (- k 1) fn-arena fn-ast-ws))))

(defun astq-scan (bytes fuel fn-arena)
  (declare (xargs :stobjs fn-arena :mode :program))
  (with-local-stobj fn-ast-ws
    (mv-let (scan fn-ast-ws)
      (astq-scan-all (fn-ast-preflight (list nil 0 (len bytes) bytes)) fuel 100000 fn-arena fn-ast-ws)
      scan)))

(defconst *astq-article*
  (append '(72 58 32 118 13 10 13 10) (astq-span-payload 700 nil)))

(assert-event
 (let ((s1 (astq-scan *astq-article* 1 fn-arena)) (s7 (astq-scan *astq-article* 7 fn-arena))
       (sall (astq-scan *astq-article* 5000 fn-arena)))
   (and (fn-ast-scan-validp s1) (fn-ast-scan-validp s7) (fn-ast-scan-validp sall)
        (equal (fn-ast-at 4 s1) 6) (equal (fn-ast-at 4 s7) 6) (equal (fn-ast-at 4 sall) 6)
        (not (fn-ast-scan-validp (astq-scan (cons 0 *astq-article*) 7 fn-arena)))
        (not (fn-ast-scan-validp (astq-scan (append *astq-article* '(65)) 7 fn-arena))))))

(assert-event
 (let* ((payload (astq-span-payload 700 nil))
        (window (list :window nil (list :payload nil 0 nil (list nil 0 (len payload) payload) t nil)))
        (want (mv-let (r s items) (fn-nsp-stuff-items 0 payload t) (declare (ignore r s)) items)))
   (and (equal (cadr (astq-render window 1 fn-arena)) want)
        (equal (cadr (astq-render window 2 fn-arena)) want)
        (equal (cadr (astq-render window 7 fn-arena)) want)
        (equal (cadr (astq-render window 5000 fn-arena)) want)
        (> (len want) 700))))
