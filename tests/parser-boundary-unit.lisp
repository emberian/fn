; Served receive/framing boundary controls, with explicit peer EOF.
; The oracle is the complete wire/close outcome written from protocol semantics;
; it does not invoke the grammar or connection handlers to predict that outcome.
(in-package "ACL2")
(include-book "../books/owed-conn")

(defun fn2-pb-text (s)
  (declare (xargs :guard (stringp s) :verify-guards nil))
  (fn2-cw-chars (coerce s 'list)))
(defun fn2-pb-lines (lines)
  (declare (xargs :verify-guards nil))
  (if (atom lines) nil
    (append (fn2-pb-text (car lines)) '(13 10) (fn2-pb-lines (cdr lines)))))
(defun fn2-pb-bytewise (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) '(:eof) (cons 1 (fn2-pb-bytewise (- n 1)))))
(defun fn2-pb-schedulep (sizes remaining)
  (declare (xargs :guard t))
  (if (atom sizes) nil
    (if (eq (car sizes) :eof)
        (and (equal remaining 0) (null (cdr sizes)))
      (and (natp remaining) (posp (car sizes)) (<= (car sizes) remaining)
           (fn2-pb-schedulep (cdr sizes) (- remaining (car sizes)))))))

(defconst *fn2-pb-greeting* '("201 fn-nntp experimental reader ready"))
(defconst *fn2-pb-mode* '("201 posting prohibited"))
; (name input expected-wire-lines). Every listed client explicitly sends EOF.
(defconst *fn2-pb-fixtures*
  (list
   (list 'idle-eof nil *fn2-pb-greeting*)
   (list 'unfinished-cr (append (fn2-pb-text "MODE READER") '(13)) *fn2-pb-greeting*)
   (list 'complete-before-eof (fn2-pb-lines '("MODE READER"))
         (append *fn2-pb-greeting* *fn2-pb-mode*))
   (list 'quit-pipeline (fn2-pb-lines '("QUIT" "AUTHINFO USER ignored" "MODE READER"))
         (append *fn2-pb-greeting* '("205 closing connection")))
   (list 'bare-lf (append (fn2-pb-text "MODE READER") '(10) (fn2-pb-lines '("QUIT")))
         (append *fn2-pb-greeting* '("501 syntax error")))
   (list 'nul-before-quit (append (fn2-pb-text "MO") '(0) (fn2-pb-lines '("DE READER" "QUIT")))
         (append *fn2-pb-greeting* '("501 syntax error")))
   (list 'utf8-before-eof (append (fn2-pb-text "GROUP ") '(194)) *fn2-pb-greeting*)))

(defun fn2-pb-antecedent (profile fixture schedule)
  (declare (xargs :verify-guards nil))
  (and (fn2-profilep profile)
       (fn2-gram-octetsp (nth 1 fixture))
       (fn2-pb-schedulep schedule (len (nth 1 fixture)))))
(defun fn2-pb-result-p (fixture result)
  (declare (xargs :verify-guards nil))
  (and (equal (car result) :quiet)
       (equal (nth 2 result) 0)
       (equal (nth 1 result) (list (list (fn2-pb-lines (nth 2 fixture)) t)))
       (fn2-conn-ledger-matches-p (nth 3 result))))
(defun fn2-pb-check-in (profile fixture schedule)
  (declare (xargs :verify-guards nil))
  (and (fn2-pb-antecedent profile fixture schedule)
       (fn2-pb-result-p fixture
        (fn2-conn-wire-run-in profile (list (list (nth 1 fixture) schedule))))))
(defun fn2-pb-check (fixture schedule)
  (declare (xargs :verify-guards nil))
  (fn2-pb-check-in *fn2-conn-wire-profile* fixture schedule))
(defun fn2-pb-coalesced (fixture)
  (declare (xargs :verify-guards nil))
  (if (atom (nth 1 fixture)) '(:eof) (list (len (nth 1 fixture)) :eof)))
(defun fn2-pb-all-coalesced (fixtures)
  (declare (xargs :verify-guards nil))
  (if (atom fixtures) t
    (and (fn2-pb-check (car fixtures) (fn2-pb-coalesced (car fixtures)))
         (fn2-pb-all-coalesced (cdr fixtures)))))
(defun fn2-pb-check-split (fixture at)
  (declare (xargs :verify-guards nil))
  (fn2-pb-check fixture (list at (- (len (nth 1 fixture)) at) :eof)))

; Full domain and complete outcome, including core stop and principal ledger.
(assert-event (fn2-pb-all-coalesced *fn2-pb-fixtures*))
; A CR split from its LF; a terminal line split from its ignored suffix;
; bytewise EOF for an unfinished multibyte sequence.
(assert-event (and (fn2-pb-check-split (nth 2 *fn2-pb-fixtures*) 12)
                   (fn2-pb-check-split (nth 3 *fn2-pb-fixtures*) 5)
                   (fn2-pb-check-split (nth 3 *fn2-pb-fixtures*) 6)
                   (fn2-pb-check (nth 6 *fn2-pb-fixtures*)
                     (fn2-pb-bytewise (len (nth 1 (nth 6 *fn2-pb-fixtures*)))))))
; Removing explicit peer EOF does NOT mean an idle peer has closed.
(assert-event
 (let* ((f (nth 1 *fn2-pb-fixtures*))
        (result (fn2-conn-wire-run (list (list (nth 1 f) nil)))))
   (and (fn2-pb-antecedent *fn2-conn-wire-profile* f (fn2-pb-coalesced f))
        (equal (nth 1 result) (list (list (fn2-pb-lines *fn2-pb-greeting*) nil)))
        (not (fn2-pb-result-p f result)))))

; EOF in an article is not an article terminator or a durable acceptance.
; This is an actual posting profile, with real genesis and an upload row.
(defconst *fn2-pb-posting-profile*
  (put-assoc-equal :groups '(("local.test" . 1))
   (put-assoc-equal :identity-arena-bytes 4096
    (put-assoc-equal :posting-interim t
     (put-assoc-equal :large-upload-windows 2
      (put-assoc-equal :pool-classes '((8 . 1024) (32 . 4096) (13 . 65536))
                       *fn2-conn-wire-profile*))))))
(defconst *fn2-pb-partial-article*
  (list 'article-dotcr-eof
        (append (fn2-pb-lines '("POST" "From: a@example.invalid" "Subject: partial"
                               "Newsgroups: local.test" "" "..stuffed")) '(46 13))
        '("200 fn-nntp experimental server ready" "340 send article to be posted")))
(assert-event
 (let* ((f *fn2-pb-partial-article*) (n (len (nth 1 f))))
   (and (fn2-pb-check-in *fn2-pb-posting-profile* f (fn2-pb-coalesced f))
        (fn2-pb-check-in *fn2-pb-posting-profile* f (list (- n 1) 1 :eof)))))
