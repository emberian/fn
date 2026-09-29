; fn: the log rotation with its I/O off the owner mutex, in the byte model
; (lane operations, 2026-09-28).
;
; The owner used to hold its mutex through the whole of P-ROTATE: the next
; segment created in journal/, preallocated, fenced, and journal/ fenced.
; Now (books/store-log-segments.lisp fn-lgs-spare-program,
; fn-lgs-rotate-program, fn-lgs-rotate-durable-program; host/native/io.lisp
; fnn-log-prepare-spare, fnn-log-rotate, fnn-log-make-durable) the spare is
; made in staging/ off the mutex, the switch under the mutex is one rename
; into journal/, and journal/ is fenced off the mutex again: by the new
; segment's first fence (fnn-log-fence) before any member written there is
; acknowledged, and by the publication (fnn-owner-publish-captured) before
; its checkpoint names the segment.  These theorems are that argument in
; books/byte-store.lisp's crash model, over the ground store of
; store-log-open-barriers (segment 1 holding an acknowledged batch):
;
;   fn-lgrs-a-staged-spare-leaves-the-journal-as-it-was   a death with the
;       spare staged (cuts rotate-created, rotate-fenced): every crash image
;       names the same segments in journal/, so the open scans segment 1 as
;       the active one; the spare's name is a staging orphan the writable
;       open sweeps (fn-lgrs-spare-name-is-swept-and-never-a-segment).
;   fn-lgrs-journal-fence-names-the-acknowledged-batch    (KEYSTONE) the
;       rename, a batch written, journal/ fenced, the batch fenced and
;       acknowledged: every crash image names the new segment with the batch
;       in it, and segment 1 as it was.
;   fn-lgrs-without-the-journal-fence-an-acknowledged-batch-is-unnamed
;       (teeth) the same without journal/'s fence: a crash image keeps the
;       acknowledged batch's octets in an inode only the staging name
;       reaches, which the open ignores and the sweep removes.  So the fence
;       before the acknowledgment is the one the argument needs.
(in-package "ACL2")
(include-book "store-log-open-barriers")
(include-book "store-log-segments")
(include-book "store-sweep")

(defun fn-lgrs-create (s dir name)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s1) (fn-bs-create s dir name :ok) (declare (ignore r)) s1))

; Segment 1 durable in journal/ with an acknowledged batch; the spare of
; segment 2 created in staging/ (inode 2), preallocated and fenced: the
; state at rotate-fenced.  Its staging name is still pending.
(defun fn-lgrs-staged-store ()
  (declare (xargs :guard t :verify-guards nil))
  (let* ((s (fn-bs-make 4 '((1 . (1 1 1 1)))
                        '((:journal ("000001.log" . 1)) (:staging))
                        nil 2))
         (s (fn-lgrs-create s :staging ".stage-segment-000002"))
         (s (fn-lgob-write s 2 '(0 0 0 0))))
    (fn-lgob-fsync-file s 2)))

; The switch (rotate-renamed), a batch appended to the new segment, then its
; fence as fnn-log-fence runs it: journal/ first when JOURNAL-FENCE
; (fnn-log-make-durable), then the segment; the members are acknowledged.
(defun fn-lgrs-rotated (journal-fence)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((s (fn-lgob-rename (fn-lgrs-staged-store)
                            :staging ".stage-segment-000002" :journal "000002.log"))
         (s (fn-lgob-write s 2 '(7 7 7 7)))
         (s (if journal-fence (fn-lgob-fsync-dir s :journal) s)))
    (fn-lgob-fsync-file s 2)))

(defthm fn-lgrs-a-staged-spare-leaves-the-journal-as-it-was
  (let ((s (fn-lgrs-staged-store)))
    (implies (fn-bs-crash-imagep s image)
             (and (null (fn-bs-durable-entry image :journal "000002.log"))
                  (equal (fn-bs-durable-entry image :journal "000001.log") 1)
                  (equal (fn-bs-durable-content image 1) '(1 1 1 1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep fn-bs-crash fn-bs-crash-select))))

; KEYSTONE.
(defthm fn-lgrs-journal-fence-names-the-acknowledged-batch
  (let ((s (fn-lgrs-rotated t)))
    (implies (fn-bs-crash-imagep s image)
             (and (equal (fn-bs-durable-entry image :journal "000002.log") 2)
                  (equal (fn-bs-durable-content image 2) '(7 7 7 7))
                  (equal (fn-bs-durable-entry image :journal "000001.log") 1)
                  (equal (fn-bs-durable-content image 1) '(1 1 1 1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep fn-bs-crash fn-bs-crash-select))))

(defthm fn-lgrs-without-the-journal-fence-an-acknowledged-batch-is-unnamed
  (let* ((s (fn-lgrs-rotated nil))
         (image (fn-bs-crash s '(:apply :drop :drop))))
    (and (fn-bs-crash-choicesp '(:apply :drop :drop) (fn-bs-pending s) (fn-bs-unit s))
         (fn-bs-crash-imagep s image)
         (equal (fn-bs-durable-content image 2) '(7 7 7 7))
         (null (fn-bs-durable-entry image :journal "000002.log"))
         (equal (fn-bs-durable-entry image :staging ".stage-segment-000002") 2)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff
                                   (s (fn-lgrs-rotated nil))
                                   (choices '(:apply :drop :drop))
                                   (image (fn-bs-crash (fn-lgrs-rotated nil)
                                                       '(:apply :drop :drop))))))))

; The spare's name (host/native/io.lisp fnn-log-spare-path) is never a
; segment the open scans, and it is a staging name the writable open's sweep
; removes (books/store-sweep.lisp fn-sn-sweep-round).
(defthm fn-lgrs-spare-name-is-swept-and-never-a-segment
  (and (null (fn-lgs-segment-index ".stage-segment-000002"))
       (equal (fn-lgs-segment-index "000002.log") 2)
       (fn-sn-staging-namep (fn-record-string-octets ".stage-segment-000002")))
  :rule-classes nil)
