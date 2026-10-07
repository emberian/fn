; fn: staging a checkpoint's delta rows into the page store's image (lane
; s-pck-host, 2026-10-07; STORAGE-PROGRAM-20261006.md section 3.3, 2b).
;
; The host holds interned rows and the payload arena.  `fn-pck-x-stage-rows'
; writes the words of each row, from the octet buffer
; (books/paged-checkpoint-exec.lisp), into `pgs-mem' at the tape position the
; previous rows ended at, one `pgs-x-write' per word (the write marks its page
; dirty).  Nothing else is written: the tail page already holds the prefix's
; words with zeros after, so the pages marked dirty are exactly the pages of
; (tail ++ delta).

(in-package "ACL2")
(include-book "paged-checkpoint-exec")
(include-book "pagestore-exec")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-pck-x-put-row (j nw p fn-octets pgs-mem)
  ; Words J..NW-1 of the buffered row to tape position P + J.
  (declare (xargs :stobjs (fn-octets pgs-mem) :verify-guards nil
                  :measure (nfix (- (nfix nw) (nfix j)))))
  (if (not (and (natp j) (natp nw) (< j nw)))
      (mv :ok pgs-mem)
    (let* ((q (+ p j))
           (lp (+ *fn-pck-root-pages* (floor q *pgs-page-words*)))
           (off (mod q *pgs-page-words*)))
      (mv-let (v pgs-mem)
        (pgs-x-write lp off (fn-pck-x-row-word j fn-octets) pgs-mem)
        (if (eq v :ok)
            (fn-pck-x-put-row (1+ j) nw p fn-octets pgs-mem)
          (mv v pgs-mem))))))

(defun fn-pck-x-stage-rows (rows p fn-arena fn-octets pgs-mem)
  ; (mv VERDICT fn-octets pgs-mem): the rows' words from tape position P on.
  (declare (xargs :stobjs (fn-arena fn-octets pgs-mem) :verify-guards nil))
  (if (atom rows)
      (mv :ok fn-octets pgs-mem)
    (let* ((fn-octets (fn-pck-x-encode-row (car rows) fn-arena fn-octets))
           (nw (fn-pck-x-row-words (fn-octets-len fn-octets))))
      (mv-let (v pgs-mem)
        (fn-pck-x-put-row 0 nw p fn-octets pgs-mem)
        (if (eq v :ok)
            (fn-pck-x-stage-rows (cdr rows) (+ p nw) fn-arena fn-octets pgs-mem)
          (mv v fn-octets pgs-mem))))))
