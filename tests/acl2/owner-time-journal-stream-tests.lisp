; Witnesses for books/owner-time-journal-stream.lisp (PKT-893, lane
; correctness-i4): the chunked read's line and exit are the whole file's.
(in-package "ACL2")
(include-book "../../books/owner-time-journal-stream")

; A whole, agreeing journal of two segments (owner-time-journal-writer-
; tests' run: a start, an issue, two clock events, a note, the return).
(defconst *otjst-es*
  '((0 0 0 1234 1 0 0)
    (1 3 10000 2000 6000 250 1)
    (2 1 12000 0 0 0 5)
    (3 1 16000 0 0 0 6)
    (4 5 16000 2 1 0 0)
    (5 4 40000 0 0 0 4)))
(defconst *otjst-file* (fn-otm-jlines (append *otjst-es* *otjst-es*)))

(defun otjst-split (xs n)
  (declare (xargs :mode :program))
  (list (take n xs) (nthcdr n xs)))

(defun otjst-chunks (xs k)
  (declare (xargs :mode :program))
  (if (<= (len xs) k) (list xs) (cons (take k xs) (otjst-chunks (nthcdr k xs) k))))

(defun otjst-agree (chunks)
  (declare (xargs :mode :program))
  (let ((st (fn-otjs-feed-all (fn-otjs-init) chunks)))
    (and (equal (fn-otjs-report st) (fn-otm-journal-report (fn-otjs-concat chunks)))
         (equal (fn-otjs-exit st) (fn-otm-journal-exit (fn-otjs-concat chunks))))))

; KEYSTONE fn-otjs-report-of-the-chunks-is-the-journal-report, reachable
; witnesses: the whole file in one chunk, split mid-line, one octet a
; chunk, and 7-octet chunks; each line is the whole file's, and that line
; is whole, two segments, twelve entries, agreeing, exit 0.
(assert-event (otjst-agree (list *otjst-file*)))
(assert-event (otjst-agree (otjst-split *otjst-file* 13)))
(assert-event (otjst-agree (otjst-chunks *otjst-file* 1)))
(assert-event (otjst-agree (otjst-chunks *otjst-file* 7)))
(assert-event (equal (fn-otjs-report (fn-otjs-feed-all (fn-otjs-init) (otjst-chunks *otjst-file* 7)))
                     (append (fn-osch-text "journal:")
                             (fn-osch-kv "entries" 12)
                             (fn-osch-kv "segments" 2)
                             (fn-osch-text " status=whole replay=agrees")
                             (list 10))))
(assert-event (equal (fn-otjs-exit (fn-otjs-feed-all (fn-otjs-init) (otjst-chunks *otjst-file* 7))) 0))

; Torn: the last line without its LF, split inside it.
(defconst *otjst-torn* (butlast *otjst-file* 1))
(assert-event (otjst-agree (otjst-split *otjst-torn* (- (len *otjst-torn*) 3))))
(assert-event (equal (fn-otjs-status (fn-otjs-feed-all (fn-otjs-init) (otjst-chunks *otjst-torn* 5))) :torn))

; Malformed: an octet that is no digit, space or LF, in the second chunk;
; the chunks after it are not read.
(defconst *otjst-bad* (append (take 20 *otjst-file*) (list 65) (nthcdr 20 *otjst-file*)))
(assert-event (otjst-agree (otjst-chunks *otjst-bad* 16)))
(assert-event (equal (fn-otjs-status (fn-otjs-feed-all (fn-otjs-init) (otjst-chunks *otjst-bad* 16))) :malformed))

; Diverged: a replayed word code altered; the exit is 1, chunked as whole.
(defconst *otjst-div* (fn-otm-jlines (list (car *otjst-es*) '(1 3 10000 2000 6000 250 2))))
(assert-event (otjst-agree (otjst-chunks *otjst-div* 3)))
(assert-event (equal (fn-otjs-exit (fn-otjs-feed-all (fn-otjs-init) (otjst-chunks *otjst-div* 3))) 1))

; The empty file: one empty chunk and no chunk agree with the whole read.
(assert-event (otjst-agree nil))
(assert-event (otjst-agree (list nil)))

; KEYSTONE fn-otjs-feed-reports-the-prefix-read (the host's step), reachable
; witnesses: after 7-octet chunks of the first 70 octets, one more 7-octet
; chunk reports the 77-octet prefix (torn mid-line, exit 1 has no meaning
; there: the status is the prefix's); the last chunk of the whole file
; reports the whole file, entries 12, exit 0.
(defun otjst-step-agree (chunks chunk)
  (declare (xargs :mode :program))
  (let ((st (fn-otjs-feed (fn-otjs-feed-all (fn-otjs-init) chunks) chunk))
        (read (append (fn-otjs-concat chunks) chunk)))
    (and (equal (fn-otjs-report st) (fn-otm-journal-report read))
         (equal (fn-otjs-exit st) (fn-otm-journal-exit read)))))
(assert-event (otjst-step-agree (otjst-chunks (take 70 *otjst-file*) 7)
                                (take 7 (nthcdr 70 *otjst-file*))))
(assert-event (let* ((cs (otjst-chunks *otjst-file* 7))
                     (st (fn-otjs-feed (fn-otjs-feed-all (fn-otjs-init) (butlast cs 1))
                                       (car (last cs)))))
                (and (otjst-step-agree (butlast cs 1) (car (last cs)))
                     (equal (fn-otjs-exit st) 0)
                     (equal (fn-otjs-status st) :whole))))
; Conclusion failure (mutation witness): the step's report differs from the
; report of the prefix WITHOUT the chunk just fed.
(assert-event (let* ((cs (otjst-chunks *otjst-file* 7))
                     (st (fn-otjs-feed (fn-otjs-feed-all (fn-otjs-init) (butlast cs 1))
                                       (car (last cs)))))
                (not (equal (fn-otjs-report st)
                            (fn-otm-journal-report (fn-otjs-concat (butlast cs 1)))))))
