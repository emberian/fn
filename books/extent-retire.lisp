; fn: releasing a dropped file's disk blocks while the owner serves (lane
; online-reclaim-2, 2026-09-29; row Q16; PRF-930).
;
; A running owner holds a read-only descriptor for every durable file an
; arena extent names (host/native/extent.lisp).  A checkpoint publication
; drops the log segments it covers (T8, fnn-log-drop) and replaces the
; previous checkpoint file, but an unlinked file's blocks come back only
; when its last descriptor closes -- so until this book, an online
; compaction (PKT-868) freed no disk until the process exited.  Freeing them
; while serving takes two steps, both decided here:
;
;   1. RESEAT.  Once the new checkpoint is durably installed, every live
;      handle whose payload the checkpoint's arena run holds is re-pointed at
;      the frame that holds it (`fn-xrt-reseat-frame', one frame per call:
;      the host preads the frame's protected prefix, the realizer's own
;      verified read, into a buffer and calls this under the owner mutex).
;      Each payload is the commit's reseat (books/payload-commit-extent.lisp
;      fn-arx-commit-reseat) with the record R the payload's own octets, so
;      nothing trusts the host's pairing of a handle with a frame position: a
;      wrong pairing finds no place and reseats nothing.  KEYSTONE
;      `fn-xrt-reseat-frame-keeps-the-arena': when the file durably holds, at
;      the frame's offset, the octets the buffer holds, the arena -- every
;      handle's payload -- is unchanged.
;
;   2. RETIRE.  A dropped file's descriptor closes only when no handle names
;      it: `fn-xrt-quiet-files' reads the concrete arena's file count column
;      (one read per retired file under the owner mutex, never a walk of the
;      arena) and excludes every file an in-flight or fenced log member
;      names.  KEYSTONE `fn-xrt-quiet-files-are-unnamed': a quiet file is
;      named by no entry at any handle.  The host closes it once no
;      off-mutex arena reader pinned at or below the generation stamped when
;      it was found quiet still runs (books/arena-reader-pins.lisp).
;
; The checkpoint frame as an extent: frame k >= 1 of the arena run is
; HEADER (37 octets), CHUNK, TRAILER with TRAILER = the frame digest of
; PREV ++ HEADER ++ CHUNK (books/store-checkpoint-codec.lisp fn-scc-seal),
; PREV the previous frame's trailer -- the 32 octets right before HEADER in
; the file.  So [frame start - 32, end of chunk) is a protected prefix whose
; trailer follows it: exactly the entry shape the extent realizer checks
; (books/payload-extent-read.lisp fn-arx-entry-ok-buffer).  The chunk is the
; batch's payloads, each its length (fn-sccr-read-nat) and its octets
; (books/store-checkpoint-arena-writer.lisp fn-scka-append-batch), in the
; order of the step's sources (`fn-xrt-step-handles').

(in-package "ACL2")
(include-book "payload-commit-extent")
(include-book "payload-arena-extent")
(include-book "store-checkpoint-reader")
(include-book "arena-reader-pins")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; 1. The reseat of one checkpoint frame.

; Where the chunk opens in the buffer: the previous trailer, then the header.
(defconst *fn-xrt-chunk-at*
  (+ *fn-frame-trailer-octets* *fn-scc-segment-header-octets*))

; The handles the writer's next step appends, in order (step 0 is the head:
; none).  A source that is not a handle (an octet list the writer copies) is
; NIL: its payload is in the chunk but no handle reseats to it.
(defun fn-xrt-srcs-handles (srcs k)
  (declare (xargs :guard (natp k)))
  (if (or (atom srcs) (zp k))
      nil
    (cons (and (natp (car srcs)) (car srcs))
          (fn-xrt-srcs-handles (cdr srcs) (1- k)))))

(defun fn-xrt-step-handles (pst)
  (declare (xargs :guard (true-listp pst)))
  (let ((index (nth 0 pst)) (srcs (nth 1 pst)) (ks (nth 2 pst)))
    (if (or (not (posp index)) (atom ks))
        nil
      (fn-xrt-srcs-handles srcs (nfix (car ks))))))

; One payload: the commit's reseat with R the payload's octets at [J, J+L)
; of the buffer, the file's copy at START + J.
(defun fn-xrt-reseat-one (h file start end j l fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :guard (and (natp file) (natp start) (natp end) (natp j) (natp l)
                              (<= (+ j l) end) (<= end (fn-octets-len fn-octets)))
                  :verify-guards nil))
  (fn-arx-commit-reseat h file
                        (list start (+ end *fn-frame-trailer-octets*) (+ start j) l)
                        (fn-oct-slice-list j (+ j l) fn-octets)
                        fn-arena))

(verify-guards fn-xrt-reseat-one)

; One frame: HANDLES the step's handles, FILE the realizer's id of the
; installed checkpoint, START the file offset of buffer cell 0 (the frame
; start less 32), the buffer's [0, END) the frame's protected prefix, I the
; cursor (the chunk start at the first call).  Answers (mv DONE fn-arena):
; DONE when every handle's length field and octets were read inside the
; prefix.
(defun fn-xrt-reseat-frame (handles file start i end fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :guard (and (natp file) (natp start) (natp i) (natp end)
                              (<= i end) (<= end (fn-octets-len fn-octets)))
                  :measure (len handles)
                  :verify-guards nil))
  (if (atom handles)
      (mv t fn-arena)
    (let ((r (fn-sccr-read-nat i end fn-octets)))
      (if (not r)
          (mv nil fn-arena)
        (let ((l (car r)) (j (cdr r)))
          (if (not (and (natp l) (natp j) (<= (+ j l) end)))
              (mv nil fn-arena)
            (let ((fn-arena (if (natp (car handles))
                                (fn-xrt-reseat-one (car handles) file start end j l
                                                   fn-octets fn-arena)
                              fn-arena)))
              (fn-xrt-reseat-frame (cdr handles) file start (+ j l) end
                                   fn-octets fn-arena))))))))

(verify-guards fn-xrt-reseat-frame
  :hints (("Goal" :use ((:instance fn-sccr-read-nat-facts))
           :in-theory (disable fn-sccr-read-nat-facts fn-xrt-reseat-one))))

; The entry the host calls: the chunk opens at *fn-xrt-chunk-at*.
(defun fn-xrt-reseat-checkpoint-frame (handles file start end fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :guard (and (natp file) (natp start) (natp end)
                              (<= end (fn-octets-len fn-octets)))))
  (if (<= *fn-xrt-chunk-at* end)
      (fn-xrt-reseat-frame handles file start *fn-xrt-chunk-at* end fn-octets fn-arena)
    (mv nil fn-arena)))

(local
 (defthm fn-xrt-len-slice
   (equal (len (fn-oct-slice-list i n fn-octets))
          (if (and (natp i) (natp n) (< i n)) (- n i) 0))
   :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets)
            :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-xrt-slice-true-listp
   (true-listp (fn-oct-slice-list i n fn-octets))
   :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets)
            :in-theory (enable fn-oct-slice-list)))))

(local
 (defun fn-xrt-ind (i j)
   (if (zp j) i (fn-xrt-ind (+ 1 (nfix i)) (1- j)))))

(local
 (defthm fn-xrt-nthcdr-slice
   (implies (and (natp i) (natp j) (natp end) (<= (+ i j) end))
            (equal (nthcdr j (fn-oct-slice-list i end fn-octets))
                   (fn-oct-slice-list (+ i j) end fn-octets)))
   :hints (("Goal" :induct (fn-xrt-ind i j)
            :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-xrt-take-slice
   (implies (and (natp a) (natp l) (natp end) (<= (+ a l) end))
            (equal (take l (fn-oct-slice-list a end fn-octets))
                   (fn-oct-slice-list a (+ a l) fn-octets)))
   :hints (("Goal" :induct (fn-xrt-ind a l)
            :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-xrt-slice-of-slice
   (implies (and (natp j) (natp l) (natp end) (<= (+ j l) end))
            (equal (take l (nthcdr j (fn-oct-slice-list 0 end fn-octets)))
                   (fn-oct-slice-list j (+ j l) fn-octets)))))

; The payload a member reads is the durable slice of the frame.
(local
 (defthm fn-xrt-member-durable
   (implies (and (natp start) (natp j) (natp l) (natp end) (<= (+ j l) end)
                 (equal (fn-durable-octets file start end)
                        (fn-oct-slice-list 0 end fn-octets)))
            (equal (fn-durable-octets file (+ start j) l)
                   (fn-oct-slice-list j (+ j l) fn-octets)))
   :hints (("Goal" :use ((:instance fn-arx-durable-slice (k j) (m l) (off start) (len end)))
            :in-theory (disable fn-arx-durable-slice)))))

; One payload's reseat keeps the arena (the commit's keystone, R the slice).
(local
 (defthm fn-xrt-one-reseat-keeps
   (implies (and (fn-arena-p fn-arena) (natp file) (natp start) (natp j) (natp l)
                 (natp end) (<= (+ j l) end)
                 (equal (fn-durable-octets file start end)
                        (fn-oct-slice-list 0 end fn-octets)))
            (equal (fn-xrt-reseat-one h file start end j l fn-octets fn-arena)
                   fn-arena))
   :hints (("Goal" :use ((:instance fn-arx-commit-reseat-keeps-the-arena
                                    (position (list start (+ end *fn-frame-trailer-octets*)
                                                    (+ start j) l))
                                    (r (fn-oct-slice-list j (+ j l) fn-octets)))
                  (:instance fn-xrt-member-durable))
            :in-theory (e/d (fn-xrt-reseat-one)
                            (fn-arx-commit-reseat-keeps-the-arena fn-arx-commit-reseat
                             fn-xrt-member-durable))))))

(local
 (defun fn-xrt-frame-ind (handles i end fn-octets)
   (declare (xargs :stobjs fn-octets :verify-guards nil :measure (len handles)))
   (if (atom handles)
       t
     (let ((r (fn-sccr-read-nat i end fn-octets)))
       (if (not r)
           t
         (fn-xrt-frame-ind (cdr handles) (+ (car r) (cdr r)) end fn-octets))))))

; KEYSTONE (PRF-930).  The reseat of a frame the file durably holds keeps
; the arena: every handle's payload after it is what it was.  Host subject:
; host/native/io.lisp fnn-extent-reseat-checkpoint calls
; fn-xrt-reseat-checkpoint-frame under the owner mutex.
(defthm fn-xrt-reseat-frame-keeps-the-arena
  (implies (and (fn-arena-p fn-arena) (natp file) (natp start) (natp i) (natp end)
                (equal (fn-durable-octets file start end)
                       (fn-oct-slice-list 0 end fn-octets)))
           (equal (mv-nth 1 (fn-xrt-reseat-frame handles file start i end fn-octets fn-arena))
                  fn-arena))
  :hints (("Goal" :induct (fn-xrt-frame-ind handles i end fn-octets)
           :do-not '(generalize eliminate-destructors fertilize)
           :in-theory (disable fn-xrt-reseat-one fn-sccr-read-nat fn-arena-p fn-oct-slice-list fn-durable-octets-unfold
                               fn-oct-slice-list-is-take-nthcdr))))

(defthm fn-xrt-reseat-checkpoint-frame-keeps-the-arena
  (implies (and (fn-arena-p fn-arena) (natp file) (natp start) (natp end)
                (equal (fn-durable-octets file start end)
                       (fn-oct-slice-list 0 end fn-octets)))
           (equal (mv-nth 1 (fn-xrt-reseat-checkpoint-frame handles file start end
                                                             fn-octets fn-arena))
                  fn-arena))
  :hints (("Goal" :in-theory (disable fn-xrt-reseat-frame))))

; -----------------------------------------------------------------------------
; 2. The retirement check, over the concrete arena's file count column
;    (books/payload-arena-extent.lisp fn-arx-file-count, lane composed-owner-4,
;    A6): one read per retired file under the owner mutex, never a walk of
;    the extent column.

; The retired files no log member in flight or fenced names (their COMPLETE
; reseats them there) and no entry of the extent column names (count 0).
(defun fn-xrt-quiet-files (retired named fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (nat-listp retired) (true-listp named))))
  (cond ((atom retired) nil)
        ((and (not (member (car retired) named))
              (equal (fn-arx-file-count (car retired) fn-arena$x) 0))
         (cons (car retired) (fn-xrt-quiet-files (cdr retired) named fn-arena$x)))
        (t (fn-xrt-quiet-files (cdr retired) named fn-arena$x))))

(local
 (defthm fn-xrt-quiet-files-member
   (implies (member f (fn-xrt-quiet-files retired named fn-arena$x))
            (and (member f retired)
                 (not (member f named))
                 (equal (fn-arx-file-count f fn-arena$x) 0)))
   :hints (("Goal" :in-theory (disable fn-arx-file-count)))))

(local
 (defthm fn-xrt-quiet-files-natp
   (implies (and (nat-listp retired)
                 (member f (fn-xrt-quiet-files retired named fn-arena$x)))
            (natp f))
   :rule-classes :forward-chaining))

; KEYSTONE (PRF-930).  Under the arena's correspondence (every export keeps
; it), a quiet file is retired, named by no log member in flight, and named
; by no entry of the extent column at any handle H: no realizer call reads
; it again once the readers that could hold an older entry are gone
; (host/native/owner.lisp fnn-owner-release-extents: the file waits at the
; generation stamped when it was found quiet until fnn-arena-clear-p,
; books/arena-reader-pins.lisp fn-arpn-clear-through-p).
(defthm fn-xrt-quiet-files-are-unnamed
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena$a)
                (nat-listp retired)
                (member f (fn-xrt-quiet-files retired named fn-arena$x)))
           (and (member f retired)
                (not (member f named))
                (not (equal (fn-arx-entry-file (nth h (nth *fn-arena$x-exti* fn-arena$x)))
                            f))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-xrt-quiet-files fn-arena$xcorr fn-arx-file-count
                               fn-arx-files-unnamed-names-none fn-arx-file-count-is-files-get)
           :use ((:instance fn-xrt-quiet-files-member)
                 (:instance fn-arx-files-unnamed-names-none (fs (list f)))
                 (:instance fn-arx-files-unnamed-p (fs (list f)))
                 (:instance fn-arx-files-unnamed-p (fs nil))))))

; -----------------------------------------------------------------------------
; 3. The release: a file a publication dropped comes back.
;
; The retirement check keeps out only a file some log member or some extent
; entry names; the pending group it goes into closes once no reader other
; than the asking publication is pinned at or below its stamp
; (host/native/owner.lisp fnn-owner-release-extents: fn-xrt-quiet-files, then
; fnn-arena-clear-p S PIN = fn-arpn-step's (:clear-except S PIN)).

(defthm fn-xrt-quiet-files-keeps-every-unnamed-retired-file
  (implies (and (member f retired)
                (not (member f named))
                (equal (fn-arx-file-count f fn-arena$x) 0))
           (member f (fn-xrt-quiet-files retired named fn-arena$x)))
  :hints (("Goal" :in-theory (disable fn-arx-file-count))))

; KEYSTONE (PRF-930, the release).  A retired file no log member in flight
; or fenced names and no entry of the extent column counts is quiet, and
; with no live reader pinned but the publication's own pin OWN, the pending
; group at any stamp S is clear: the host closes the file's descriptor in
; the same release (its blocks come back while the owner serves).
(defthm fn-xrt-dropped-file-is-released
  (implies (and (member f retired)
                (not (member f named))
                (equal (fn-arx-file-count f fn-arena$x) 0)
                (natp s)
                (natp own)
                (fn-arpn-held-p own (second st))
                (atom (fn-arpn-unpin-at own (second st))))
           (and (member f (fn-xrt-quiet-files retired named fn-arena$x))
                (equal (mv-nth 1 (fn-arpn-step st (list :clear-except s own))) t)))
  :hints (("Goal" :in-theory (disable fn-xrt-quiet-files fn-arx-file-count
                                      fn-arpn-unpin-at fn-arpn-held-p)
           :use ((:instance fn-xrt-quiet-files-keeps-every-unnamed-retired-file)))))
