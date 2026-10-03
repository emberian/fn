; Actual formatting/navigation consumers of the classified catalog writer.
; These are command-helper acceptance fixtures; production owner/R wiring is
; distinct and not established by this program-mode fixture.
(in-package "ACL2")
(include-book "../../books/served-available-commands")
(include-book "catalog-available-readers-tests")

(defun cav-av-articles (i v fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (if (zp i) nil
    (let ((seq (- i 1)))
      (if (fn-cat-visible-at seq v fn-cat)
          (cons (fn-av-held-article seq fn-cat) (cav-av-articles seq v fn-cat))
        (cav-av-articles seq v fn-cat)))))

(defun cav-av-octets (result)
  (declare (xargs :mode :program))
  (cadr (car (fn-nntp-result-effects result))))

(defun cav-av-facts-completep (articles fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (if (consp articles)
      (let ((facts (fn-scol-facts (car articles) fn-cat)))
        (and (fn-hnov-p (fn-hf-nov facts))
             (equal facts (fn-held-facts-of (fn-nntp-article-bytes (car articles) fn-arena)))
             (cav-av-facts-completep (cdr articles) fn-arena fn-cat)))
    t))

(defun cav-av-fill (i n survivors fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (if (>= i n) (mv fn-arena fn-cat)
    (let* ((tomb (not (member-equal (+ 1 i) survivors)))
           (wire (fn-held-wire (cav-row i tomb) (cav-bytes i tomb))))
      (mv-let (held fn-arena) (fn-cat-intern-list wire nil 0 fn-arena)
        (let ((fn-cat (fn-cat-commit held fn-cat)))
          (cav-av-fill (+ 1 i) n survivors fn-arena fn-cat))))))

(defun cav-av-run (survivors fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let ((fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat) (cav-av-fill 0 34 survivors fn-arena fn-cat)
      (let* ((archive (fn-make-state '("fn.available") '(("fn.available" . 35))
                                     (cav-av-articles 34 34 fn-cat) 0 nil nil))
             (available (fn-nntp-available-archive archive fn-arena))
             (session (fn-nntp-make-session t "fn.available" 1 t))
             (group (fn-av-nntp-group-result-cat session archive "fn.available" 34 fn-cat))
             (listing (fn-av-nntp-listgroup-command-cat session archive nil 34 fn-cat))
             (next (fn-av-nntp-next-or-last-cat session archive :next 34 fn-arena fn-cat))
             (last (fn-av-nntp-next-or-last-cat
                     (fn-nntp-make-session t "fn.available" 34 t) archive :last 34 fn-arena fn-cat))
             (active (fn-av-nntp-list-active-cat session archive nil nil 34 fn-cat))
             (counts (fn-av-nntp-list-counts-command-cat session archive nil nil 34 fn-cat)))
        (mv (list
              (cav-av-facts-completep (fn-state-articles archive) fn-arena fn-cat)
              (fn-statep archive) (fn-statep available)
              (equal group (fn-nntp-group-result session available "fn.available"))
              (equal listing (fn-nntp-listgroup-command session available nil))
              (equal next (fn-nntp-next-or-last session available :next fn-arena))
              (equal last (fn-nntp-next-or-last
                           (fn-nntp-make-session t "fn.available" 34 t)
                           available :last fn-arena))
              (equal active (fn-nntp-list-active session available (fn-state-groups available)))
              (equal counts (fn-nntp-list-counts-command session available nil nil))
              (fn-nntp-session-current (fn-nntp-result-session group))
              (cav-av-octets group) (cav-av-octets listing)
              (fn-nntp-session-current (fn-nntp-result-session next))
              (cav-av-octets next)
              (fn-nntp-session-current (fn-nntp-result-session last))
              (cav-av-octets last) (cav-av-octets active) (cav-av-octets counts)
              (fn-cat-group-number "fn.available" 2 fn-cat)
              (fn-cat-msgid-seqs "<1@available.test>" fn-cat))
            fn-cat fn-arena)))))

(defun cav-av-local-cat (survivors fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (with-local-stobj fn-cat
    (mv-let (answer fn-cat fn-arena) (cav-av-run survivors fn-arena fn-cat)
      (mv answer fn-arena))))

(defun cav-av-local (survivors)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena) (cav-av-local-cat survivors fn-arena) answer)))

; Full raw and projected archive state premises and decided fact/byte
; correspondence are asserted before comparing every selected actual result.
(assert-event
 (let ((answer (cav-av-local '(1 34))))
   (and (equal (take 9 answer) '(t t t t t t t t t))
        (equal (nth 9 answer) 1)
        (equal (nth 12 answer) 34)
        (equal (nth 14 answer) 1)
        (equal (nth 18 answer) 1)
        (equal (nth 19 answer) '(1)))))

(assert-event
 (let ((answer (cav-av-local nil)))
   (and (equal (take 9 answer) '(t t t t t t t t t))
        (not (nth 9 answer))
        (equal (nth 12 answer) 1)
        (equal (nth 14 answer) 34)
        (equal (nth 18 answer) 1)
        (equal (nth 19 answer) '(1)))))
