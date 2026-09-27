; fn: witnesses and teeth for books/store-recover-stream.lisp (lane
; recover-memory, PKT-823): the chunked full replay the host runs
; (host/native/io.lisp fnn-bridge-recover -> host/store-node-host.lisp
; fn-store-sn-recover-step -> fn-srs-step).
;
; The history is three real journal records (fn-store-event-encode of
; records the codec decodes back exactly); the arena is a local one.
(in-package "ACL2")
(include-book "../../books/store-recover-stream")

(defconst *srst-groups* '("fn.test"))
(defconst *srst-records*
  (list (fn-record-make 0 0 0 "<r0@example>" '(65 66 67) *srst-groups*
                        "p0" "c0" "e0" 2 841000000)
        (fn-record-make 1 1 0 "<r1@example>" '(68 69) *srst-groups*
                        "p1" "c1" "e1" 2 841000001)
        (fn-record-make 2 2 0 "<r2@example>" '(70) *srst-groups*
                        "p2" "c2" "e2" 2 841000002)))
(assert-event (and (fn-record-p (nth 0 *srst-records*))
                   (fn-record-p (nth 1 *srst-records*))
                   (fn-record-p (nth 2 *srst-records*))))
(defconst *srst-r0* (fn-store-event-encode (nth 0 *srst-records*)))
(defconst *srst-r1* (fn-store-event-encode (nth 1 *srst-records*)))
(defconst *srst-r2* (fn-store-event-encode (nth 2 *srst-records*)))
(defconst *srst-history* (list *srst-r0* *srst-r1* *srst-r2*))
; The records decode back exactly (what the journal replay reads).
(assert-event (equal (fn-srs-decode *srst-history*) *srst-records*))

; The fold and the one step, each over a fresh local arena; the answer is the
; rows (newest first, or :bad) and the arena's payloads.
(defun srst-arena-list (i fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil
                  :measure (nfix (- (fn-arena-count fn-arena) (nfix i)))))
  (if (and (natp i) (< i (fn-arena-count fn-arena)))
      (cons (fn-arena-payload i fn-arena) (srst-arena-list (1+ i) fn-arena))
    nil))
(defun srst-steps (chunks)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (acc fn-arena)
      (fn-srs-steps chunks nil fn-arena)
      (list acc (srst-arena-list 0 fn-arena)))))
(defun srst-one (chunks)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (acc fn-arena)
      (fn-srs-step nil (fn-srs-concat chunks) fn-arena)
      (list acc (srst-arena-list 0 fn-arena)))))
(defun srst-intern-of-decode (octet-records)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (fn-intern-events (fn-srs-decode octet-records) nil 0 fn-arena)
      (list rows (srst-arena-list 0 fn-arena)))))

; The keystone's conclusion over its answers (fn-srs-same's reading).
(defun srst-conclusion (steps one)
  (declare (xargs :verify-guards nil))
  (and (iff (eq (car steps) :bad) (eq (car one) :bad))
       (implies (not (eq (car one) :bad)) (equal steps one))))

; -----------------------------------------------------------------------------
; Reachable positive witnesses: the host's chunkings of a real history.
; Antecedent: every chunk a true list.  Conclusion: the same rows and arena
; as one step; not :bad; the rows oldest first are the intern of the decode
; and the arena holds the three payloads in order.

(defconst *srst-chunkings*
  (list (list *srst-history*)
        (list (list *srst-r0* *srst-r1*) (list *srst-r2*))
        (list (list *srst-r0*) (list *srst-r1*) (list *srst-r2*))
        (list nil (list *srst-r0*) nil (list *srst-r1* *srst-r2*))))

(defun srst-all-hold (cs)
  (declare (xargs :verify-guards nil))
  (if (atom cs)
      t
    (let ((chunks (car cs)))
      (and (fn-srs-chunksp chunks)
           (equal (fn-srs-concat chunks) *srst-history*)
           (not (eq (car (srst-one chunks)) :bad))
           (srst-conclusion (srst-steps chunks) (srst-one chunks))
           (srst-all-hold (cdr cs))))))
(assert-event (srst-all-hold *srst-chunkings*))

(assert-event
 (let ((one (srst-one (list *srst-history*)))
       (ref (srst-intern-of-decode *srst-history*)))
   (and (equal (reverse (car one)) (car ref))
        (equal (cadr one) (cadr ref))
        (equal (cadr one) '((65 66 67) (68 69) (70)))
        (equal (len (car one)) 3))))

; A refused history: the second chunk's record does not decode (one octet
; flipped).  Antecedent holds; both answers are :bad (conclusion holds).
(defconst *srst-corrupt* (cons (logxor 1 (car *srst-r1*)) (cdr *srst-r1*)))
(assert-event (equal (fn-srs-decode (list *srst-corrupt*)) :bad))
(assert-event
 (let ((chunks (list (list *srst-r0*) (list *srst-corrupt* *srst-r2*))))
   (and (fn-srs-chunksp chunks)
        (eq (car (srst-steps chunks)) :bad)
        (eq (car (srst-one chunks)) :bad)
        (srst-conclusion (srst-steps chunks) (srst-one chunks)))))

; -----------------------------------------------------------------------------
; Hypothesis removal (fn-srs-chunksp): a chunk that is not a true list.  The
; hypothesis fails; the fold refuses the dotted chunk while one step over the
; concatenation (which normalizes each chunk) opens: the conclusion fails.
(assert-event
 (let ((chunks (list (cons *srst-r0* 5) (list *srst-r1* *srst-r2*))))
   (and (not (fn-srs-chunksp chunks))
        (eq (car (srst-steps chunks)) :bad)
        (not (eq (car (srst-one chunks)) :bad))
        (not (srst-conclusion (srst-steps chunks) (srst-one chunks))))))

; The quantum: a chunk closes at 1 MiB of record octets, and a record above
; it is a chunk by itself (the host's loop takes one record before asking).
(assert-event (and (not (fn-srs-chunk-fullp 0))
                   (not (fn-srs-chunk-fullp 1048575))
                   (fn-srs-chunk-fullp 1048576)
                   (fn-srs-chunk-fullp 10485760)))
