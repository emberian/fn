; D4 evidence for the article input feed (fn2/books/upload-feed.lisp;
; fn2/docs/d-machines-nntp.md section 14.2). The expected chunk is the
; source itself; the block on the wire is written here by an independent
; dot-stuffing (H's framing.py: stuff, then ".CRLF"), never by the feed.
; Every source is fed whole, at every split point of its block, with the
; smallest budget, and into two small chunks (the :full switch). RX and the
; chunk have different owners, as a connection and its upload do.
; Teeth of fn2-upload-source-exact: a feed that does not unstuff (the
; negative control below) gives a different chunk.
; Run: sh fn2/tools/certify.sh tests/upload-feed-unit.lisp
(in-package "ACL2")
(include-book "../books/upload-feed")

(defun fn2-ufu-octets (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (atom cs) nil (cons (char-code (car cs)) (fn2-ufu-octets (cdr cs)))))
(defun fn2-ufu-crlf (lines)
  (declare (xargs :guard (string-listp lines)))
  (if (atom lines) ""
    (concatenate 'string (car lines) (coerce (list (code-char 13) (code-char 10)) 'string)
                 (fn2-ufu-crlf (cdr lines)))))
; framing.py's stuff: a dot at the start of the data or after CRLF is doubled.
(defun fn2-ufu-stuff (xs bol)
  (declare (xargs :guard (true-listp xs)))
  (cond ((atom xs) nil)
        ((and bol (equal (car xs) 46)) (list* 46 46 (fn2-ufu-stuff (cdr xs) nil)))
        ((and (equal (car xs) 13) (consp (cdr xs)) (equal (cadr xs) 10))
         (list* 13 10 (fn2-ufu-stuff (cddr xs) t)))
        (t (cons (car xs) (fn2-ufu-stuff (cdr xs) nil)))))
(defun fn2-ufu-block (source) (declare (xargs :verify-guards nil)) (append (fn2-ufu-stuff source t) (list 46 13 10)))

(defun fn2-ufu-put (octets slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom octets) fn2-pool
    (mv-let (code fn2-pool) (fn2-gram-put (nfix (car octets)) slot gen 1 1 1 fn2-pool)
      (declare (ignore code))
      (fn2-ufu-put (cdr octets) slot gen fn2-pool))))
(defun fn2-ufu-read (k n slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix (- (nfix n) (nfix k)))))
  (if (>= (nfix k) (nfix n)) nil
    (mv-let (ok b) (fn2-gram-read slot gen (nfix k) 2 2 2 fn2-pool)
      (cons (if ok b 999) (fn2-ufu-read (+ 1 (nfix k)) n slot gen fn2-pool)))))

; Feed until a stop other than :budget, switching to chunk B at :full.
(defun fn2-ufu-drive (fuel left i mode discard rslot rgen a agen b bgen cur fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv :fuel i mode discard cur fn2-pool)
    (mv-let (status i mode discard copied fn2-pool)
      (if cur (fn2-upload-feed left i mode discard rslot rgen 1 1 1 b bgen 2 2 2 fn2-pool)
        (fn2-upload-feed left i mode discard rslot rgen 1 1 1 a agen 2 2 2 fn2-pool))
      (declare (ignore copied))
      (cond ((eq status :budget) (fn2-ufu-drive (- fuel 1) left i mode discard rslot rgen a agen b bgen cur fn2-pool))
            ((and (eq status :full) (not cur))
             (fn2-ufu-drive (- fuel 1) left i mode discard rslot rgen a agen b bgen t fn2-pool))
            (t (mv status i mode discard cur fn2-pool))))))

; Run: the block arrives as its first SPLIT octets then the rest, followed
; by TRAIL (a pipelined command). Returns (status consumed discard chunk).
(defun fn2-ufu-run (block trail split left chunk)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool
    (mv-let (result fn2-pool)
      (b* ((fn2-pool (fn2-pool-init (list (cons 2 chunk) (cons 1 8192)) 1 1000 fn2-pool))
           ((mv & rslot rgen fn2-pool) (fn2-pool-reserve 1 1 1 1 fn2-pool))
           ((mv & a agen fn2-pool) (fn2-pool-reserve 0 2 2 2 fn2-pool))
           ((mv & b bgen fn2-pool) (fn2-pool-reserve 0 2 2 2 fn2-pool))
           (wire (append block trail))
           (k (min split (len wire)))
           (fn2-pool (fn2-ufu-put (take k wire) rslot rgen fn2-pool))
           ((mv status i mode discard cur fn2-pool) (fn2-ufu-drive 100000 left 0 0 nil rslot rgen a agen b bgen nil fn2-pool))
           (fn2-pool (fn2-ufu-put (nthcdr k wire) rslot rgen fn2-pool))
           ((mv status i & discard & fn2-pool)
            (if (eq status :need-more) (fn2-ufu-drive 100000 left i mode discard rslot rgen a agen b bgen cur fn2-pool)
              (mv status i mode discard cur fn2-pool)))
           (chunk (append (fn2-ufu-read 0 (fn2-gram-fill a fn2-pool) a agen fn2-pool)
                          (fn2-ufu-read 0 (fn2-gram-fill b fn2-pool) b bgen fn2-pool))))
        (mv (list status i discard chunk) fn2-pool))
      result)))

(defun fn2-ufu-splits (k block trail expect)
  (declare (xargs :verify-guards nil :measure (nfix (- (+ 1 (len block)) (nfix k)))))
  (cond ((< (len block) (nfix k)) t)
        ((not (equal (fn2-ufu-run block trail (nfix k) 4096 4096) expect))
         (cw "split ~x0: ~x1~%" k (fn2-ufu-run block trail (nfix k) 4096 4096)))
        (t (fn2-ufu-splits (+ 1 (nfix k)) block trail expect))))
; A well-formed source: its chunk is the source, whole, split, at budget 1,
; and across two 64-octet chunks; the trailing command is not consumed.
(defun fn2-ufu-good (lines)
  (declare (xargs :verify-guards nil))
  (let* ((source (fn2-ufu-octets (coerce (fn2-ufu-crlf lines) 'list)))
         (block (fn2-ufu-block source))
         (trail (fn2-ufu-octets (coerce "QUIT" 'list)))
         (expect (list :terminator (len block) nil source)))
    (and (or (equal (fn2-ufu-run block trail 100000 4096 4096) expect) (cw "whole ~x0~%" lines))
         (or (equal (fn2-ufu-run block trail 100000 1 4096) expect) (cw "budget 1 ~x0~%" lines))
         (or (< 128 (len source)) (equal (fn2-ufu-run block trail 100000 4096 64) expect) (cw "two chunks ~x0~%" lines))
         (fn2-ufu-splits 0 block trail expect))))
; A malformed block: drained to its terminator, DISCARD set, at every split.
(defun fn2-ufu-bad (wire-block)
  (declare (xargs :verify-guards nil))
  (let ((block (fn2-ufu-octets (coerce wire-block 'list))))
    (and (equal (car (fn2-ufu-run block nil 100000 4096 4096)) :terminator)
         (equal (cadr (fn2-ufu-run block nil 100000 4096 4096)) (len block))
         (equal (caddr (fn2-ufu-run block nil 100000 4096 4096)) t)
         (fn2-ufu-splits 0 block nil (fn2-ufu-run block nil 100000 4096 4096)))))

(defun fn2-ufu-crlf-string (s) (declare (xargs :verify-guards nil))
  (concatenate 'string s (coerce (list (code-char 13) (code-char 10)) 'string)))

(defun fn2-ufu-fixtures ()
  (declare (xargs :verify-guards nil))
  (and (fn2-ufu-good nil)
       (fn2-ufu-good '("From: a" "Subject: s" "Newsgroups: g" "" "body"))
       (fn2-ufu-good '("Subject: dots" "" "." ".." "...x" ".leading" "" "trailing ."))
       (fn2-ufu-good (list "Subject: long" "" (coerce (make-list 300 :initial-element #\y) 'string) "end"))
       (fn2-ufu-good (list "X: binary" "" (coerce (list (code-char 255) (code-char 1) (code-char 128)) 'string)))
       ;; framing errors (framing.py): bare LF, bare CR, NUL, an unescaped leading dot
       (fn2-ufu-bad (concatenate 'string "a" (coerce (list (code-char 10)) 'string) "b" (fn2-ufu-crlf-string "") (fn2-ufu-crlf-string ".")))
       (fn2-ufu-bad (concatenate 'string "a" (coerce (list (code-char 13)) 'string) "b" (fn2-ufu-crlf-string "") (fn2-ufu-crlf-string ".")))
       (fn2-ufu-bad (concatenate 'string "a" (coerce (list (code-char 0)) 'string) (fn2-ufu-crlf-string "b") (fn2-ufu-crlf-string ".")))
       (fn2-ufu-bad (concatenate 'string (fn2-ufu-crlf-string "x") (fn2-ufu-crlf-string ".bad") (fn2-ufu-crlf-string ".")))))
(assert-event (fn2-ufu-fixtures))

; Negative control: a source with a leading dot line, compared as if the
; feed copied the stuffed octets verbatim, does not match what it wrote.
(assert-event
 (let* ((source (fn2-ufu-octets (coerce (fn2-ufu-crlf '(".hidden")) 'list)))
        (block (fn2-ufu-block source)))
   (not (equal (fn2-ufu-run block nil 100000 4096 4096)
               (list :terminator (len block) nil (fn2-ufu-stuff source t))))))
