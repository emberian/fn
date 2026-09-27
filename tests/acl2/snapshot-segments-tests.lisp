; fn: witnesses and teeth for the snapshot container
; (books/snapshot-segments.lisp; lane snapshot-open).  Attachments evaluate
; in assert-event and defun bodies: the digest is fn-sha256's.

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/snapshot-segments")
(include-book "../../books/crypto-attach")

(defconst *t-w* '(8 1))
(defconst *t-s1* '((5 6 7) (1 2 3 4 5)))
(defconst *t-s2* '((5 6 7 8 9) (1 2 3 4 5 6)))
(defconst *t-meta* '(9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9
                     9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9 9))

(defun t-file (states max)
  (declare (xargs :mode :program))
  (mv-let (o d)
    (fn-snap-writes *fn-snap-genesis* '(0 0) states
                    (make-list (len states) :initial-element *t-meta*) *t-w* max)
    (declare (ignore d))
    o))

(defun t-scan (x)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (r fn-octets)
      (let ((fn-octets (fn-octets-from-list x fn-octets)))
        (mv-let (reason last)
          (fn-snap-scan 0 (len x) *fn-snap-genesis* '(0 0) nil nil *t-w* fn-octets)
          (mv (list reason (and last (fn-snap-denotes last *t-w* x)) (nth 0 last))
              fn-octets)))
      r)))

(defconst *t-states* (list *t-s1* *t-s2*))

; Reachable positive witness (fn-snap-scan over what fn-snap-writes wrote):
; two writes, the second appending two elements to column 1 and one to the
; byte pool; chunked two elements a segment (MAX 2) and unchunked (MAX
; 100): both scan to :end and the last commit denotes the second state.
(assert-event (equal (t-scan (t-file *t-states* 2)) (list :end *t-s2* 750)))
(assert-event (equal (t-scan (t-file *t-states* 100)) (list :end *t-s2* 558)))

; The torn tail of the second write (its last three octets never written):
; :torn, and the last commit is the FIRST write's, which denotes S1 (the
; open falls back to it and replays a longer log tail).
(assert-event
 (let ((f (t-file *t-states* 2)))
   (equal (t-scan (take (- (len f) 3) f)) (list :torn *t-s1* 477))))

; A torn write that ends at a segment boundary: data segments after the
; last commit are never used (:end, last commit still S1's).
(assert-event
 (let ((f (t-file *t-states* 2)))
   (equal (t-scan (take (- (len f) (+ 64 (* 8 2) 48)) f))
          (list :end *t-s1* 477))))

; Mutation witnesses (corrupted file, labelled): an octet of the FIRST
; segment's body changed -> :digest before any commit (nothing is used);
; an octet inside the second write changed -> :digest, the first commit
; stands.  (That a change is DETECTED is the attached SHA-256's property,
; A-CRYPTO; the logic only says an accepted segment's digest verified.)
(assert-event
 (let ((f (t-file *t-states* 2)))
   (equal (t-scan (update-nth 40 (mod (1+ (nth 40 f)) 256) f))
          (list :digest nil nil))))
(assert-event
 (let ((f (t-file *t-states* 2)))
   (equal (t-scan (update-nth (- (len f) 50) (mod (1+ (nth (- (len f) 50) f)) 256) f))
          (list :digest *t-s1* 477))))

; Mutation: the second write's segments spliced out (a reorder/splice):
; the commit after them states lengths the scan did not build -> refused
; (:digest: its chain names a predecessor that is not there).
(assert-event
 (let* ((f (t-file *t-states* 100))
        (w1 (t-file (list *t-s1*) 100))
        (tail (nthcdr (- (len f) (+ 64 (* 8 2) 48)) f)))
   (equal (car (t-scan (append w1 tail))) :digest)))
