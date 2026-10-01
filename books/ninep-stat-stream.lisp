; Base9P stat encoding, one concrete output octet per action.
; stat(5): nested size2, type2/dev4/qid13/mode4/times8/length8,
; name string, uid/gid/muid strings. Empty owner names and zero times are
; the immutable presentation policy. Source/QID issuance is external.
(in-package "ACL2")
(include-book "ninep-version")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-9pst-le-byte (value index)
 (declare (xargs :guard t))
 (if (not (and (natp value) (natp index) (< index 8))) 0
  (mod (floor value (case index
                     (0 1) (1 256) (2 65536) (3 16777216)
                     (4 4294967296) (5 1099511627776)
                     (6 281474976710656) (otherwise 72057594037927936))) 256)))

; Cursor7: tag/name/actual QID/length/next byte/total bytes/directory mode.
; A codec range refusal does not truncate the stored name or article.
(defun fn-9pst-begin (name qid length)
 (declare (xargs :guard t))
 (let ((kind (fn-9p-metadata-at 0 qid)) (version (fn-9p-metadata-at 1 qid))
       (path (fn-9p-metadata-at 2 qid)))
  (if (not (and (stringp name) (<= (+ 49 (length name)) 65535)
                (member-equal kind '(0 128)) (natp version) (< version 4294967296)
                (natp path) (< path 18446744073709551616)
                (natp length) (< length 18446744073709551616)
                (or (equal kind 0) (equal length 0))))
      (mv :stat-unrepresentable nil)
    (mv :stat (list :ninep-stat name qid length 0 (+ 49 (length name))
                    (if (equal kind 128) 2147484013 292))))))

(defun fn-9pst-ready-p (cursor)
 (declare (xargs :guard t))
 (let* ((name (fn-9p-metadata-at 1 cursor)) (qid (fn-9p-metadata-at 2 cursor))
        (length (fn-9p-metadata-at 3 cursor)) (position (fn-9p-metadata-at 4 cursor))
        (total (fn-9p-metadata-at 5 cursor)) (mode (fn-9p-metadata-at 6 cursor)))
  (and (eq (fn-9p-metadata-at 0 cursor) :ninep-stat) (stringp name)
       (natp total) (equal total (+ 49 (length name))) (<= total 65535)
       (natp position) (<= position total)
       (member-equal (fn-9p-metadata-at 0 qid) '(0 128))
       (natp (fn-9p-metadata-at 1 qid)) (< (fn-9p-metadata-at 1 qid) 4294967296)
       (natp (fn-9p-metadata-at 2 qid)) (< (fn-9p-metadata-at 2 qid) 18446744073709551616)
       (natp length) (< length 18446744073709551616)
       (if (equal (fn-9p-metadata-at 0 qid) 128)
           (and (equal length 0) (equal mode 2147484013)) (equal mode 292)))))

(defun fn-9pst-byte (cursor)
 (declare (xargs :guard (fn-9pst-ready-p cursor)))
 (let* ((name (fn-9p-metadata-at 1 cursor)) (qid (fn-9p-metadata-at 2 cursor))
        (position (fn-9p-metadata-at 4 cursor)))
  (cond ((< position 2) (fn-9pst-le-byte (- (fn-9p-metadata-at 5 cursor) 2) position))
        ((< position 8) 0)
        ((equal position 8) (fn-9p-metadata-at 0 qid))
        ((< position 13) (fn-9pst-le-byte (fn-9p-metadata-at 1 qid) (- position 9)))
        ((< position 21) (fn-9pst-le-byte (fn-9p-metadata-at 2 qid) (- position 13)))
        ((< position 25) (fn-9pst-le-byte (fn-9p-metadata-at 6 cursor) (- position 21)))
        ((< position 33) 0)
        ((< position 41) (fn-9pst-le-byte (fn-9p-metadata-at 3 cursor) (- position 33)))
        ((< position 43) (fn-9pst-le-byte (length name) (- position 41)))
        ((< position (+ 43 (length name))) (char-code (char name (- position 43))))
        (t 0))))

; Each call performs at most one append to the actual concrete octet buffer.
; Buffer reserve/allocation is paid by the operation before this entry.
(defun fn-9pst-emit-step (cursor limit fn-octets)
 (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :in-theory (e/d (fn-9pst-ready-p fn-cbor-octetp)
                                      (fn-9pst-byte fn-9p-metadata-at fn-octets-len))))))
 (cond ((not (and (fn-9pst-ready-p cursor) (natp limit)))
        (mv :recovery-required cursor fn-octets))
       ((equal (fn-9p-metadata-at 4 cursor) (fn-9p-metadata-at 5 cursor))
        (mv :complete cursor fn-octets))
       ((>= (fn-octets-len fn-octets) limit) (mv :yield cursor fn-octets))
       (t (let ((byte (fn-9pst-byte cursor)))
            (if (not (and (integerp byte) (<= 0 byte) (< byte 256)))
                (mv :source-unrepresentable cursor fn-octets)
              (let* ((fn-octets (fn-octets-append-octet byte fn-octets))
                     (next (list :ninep-stat (fn-9p-metadata-at 1 cursor)
                                  (fn-9p-metadata-at 2 cursor) (fn-9p-metadata-at 3 cursor)
                                  (1+ (fn-9p-metadata-at 4 cursor))
                                  (fn-9p-metadata-at 5 cursor) (fn-9p-metadata-at 6 cursor))))
               (mv :yield next fn-octets)))))))

(local (defthm fn-9pst-emit-never-reply-ready
 (not (equal (car (fn-9pst-emit-step cursor limit fn-octets)) :reply-ready))
 :hints (("Goal" :in-theory (e/d (fn-9pst-emit-step)
                                     (fn-9pst-byte fn-9pst-ready-p fn-9p-metadata-at))))))

; Only complete stat entries enter a directory reply. A small Tread count
; returns a representability error; it does not emit a partial entry or EOF.
(defun fn-9pst-reply-begin (kind tag msize count stat)
 (declare (xargs :guard t))
 (let ((header (if (eq kind :stat) 9 11)) (size (fn-9p-metadata-at 5 stat)))
  (if (not (and (member-eq kind '(:stat :directory-read))
                (natp tag) (< tag 65535) (fn-9p-profile-msizep msize)
                (fn-9pst-ready-p stat) (equal (fn-9p-metadata-at 4 stat) 0)
                (natp size) (<= (+ header size) msize)
                (or (eq kind :stat) (and (natp count) (<= size count)))))
      (mv :reply-unrepresentable nil)
    (mv :reply (list :ninep-stat-reply kind tag stat 0 (+ header size))))))

(defun fn-9pst-reply-step (cursor fn-octets)
 (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :in-theory
                      (disable fn-9pst-ready-p fn-9pst-le-byte fn-9pst-emit-step
                               fn-9p-metadata-at fn-octets-len)))))
 (let* ((kind (fn-9p-metadata-at 1 cursor)) (tag (fn-9p-metadata-at 2 cursor))
        (stat (fn-9p-metadata-at 3 cursor)) (pos (fn-9p-metadata-at 4 cursor))
        (total (fn-9p-metadata-at 5 cursor)) (header (if (eq kind :stat) 9 11)))
  (cond
   ((not (and (eq (fn-9p-metadata-at 0 cursor) :ninep-stat-reply)
              (member-eq kind '(:stat :directory-read)) (natp tag) (< tag 65535)
              (fn-9pst-ready-p stat) (natp (fn-9p-metadata-at 5 stat)) (natp pos) (natp total)
              (equal total (+ header (fn-9p-metadata-at 5 stat)))
              (<= pos total) (equal pos (fn-octets-len fn-octets))
              (equal (fn-9p-metadata-at 4 stat) (if (< pos header) 0 (- pos header)))))
    (mv :recovery-required cursor fn-octets))
   ((equal pos total) (mv :reply-ready cursor fn-octets))
   ((< pos header)
    (let* ((byte (cond ((< pos 4) (fn-9pst-le-byte total pos))
                       ((equal pos 4) (if (eq kind :stat) 125 117))
                       ((< pos 7) (fn-9pst-le-byte tag (- pos 5)))
                       (t (fn-9pst-le-byte (fn-9p-metadata-at 5 stat) (- pos 7)))))
           (fn-octets (if (fn-cbor-octetp byte) (fn-octets-append-octet byte fn-octets) fn-octets)))
     (if (fn-cbor-octetp byte)
         (mv :yield (list :ninep-stat-reply kind tag stat (1+ pos) total) fn-octets)
       (mv :recovery-required cursor fn-octets))))
   ((not (equal (- pos header) (fn-9p-metadata-at 4 stat)))
    (mv :recovery-required cursor fn-octets))
   (t (mv-let (word next fn-octets) (fn-9pst-emit-step stat total fn-octets)
       (mv word (if (equal (fn-9p-metadata-at 4 next) (fn-9p-metadata-at 4 stat)) cursor
                  (list :ninep-stat-reply kind tag next (1+ pos) total)) fn-octets))))))

(defthm fn-9pst-reply-ready-is-complete-integral-stat
 (implies (eq (mv-nth 0 (fn-9pst-reply-step cursor fn-octets)) :reply-ready)
  (and (equal (fn-octets-len fn-octets) (fn-9p-metadata-at 5 cursor))
       (equal (fn-9p-metadata-at 5 cursor)
              (+ (if (eq (fn-9p-metadata-at 1 cursor) :stat) 9 11)
                 (fn-9p-metadata-at 5 (fn-9p-metadata-at 3 cursor))))
       (equal (fn-9p-metadata-at 4 (fn-9p-metadata-at 3 cursor))
              (fn-9p-metadata-at 5 (fn-9p-metadata-at 3 cursor)))
       (equal (mv-nth 1 (fn-9pst-reply-step cursor fn-octets)) cursor)
       (equal (mv-nth 2 (fn-9pst-reply-step cursor fn-octets)) fn-octets)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-9pst-reply-step)
                                (fn-9pst-emit-step fn-9pst-ready-p fn-9p-profile-msizep
                                 fn-9pst-le-byte fn-9p-metadata-at)))))
