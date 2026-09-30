; PRF-1107: bounded current-format root -> directory -> table -> data reader.
; Library composition under construction; no served-path activation claim.
(in-package "ACL2")
(include-book "history-page-reader-verdict")
(include-book "history-page-reader-io")
(include-book "history-record-cursor")
(include-book "pagestore-digest-cursor")
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm fn-hsr-word-state-naturals
   (implies (fn-hrcur-wordp used acc) (and (natp used) (natp acc)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-hrcur-wordp)))))

(defun fn-hsr-put (i value c)
  (declare (xargs :guard (natp i)))
  (if (zp i) (cons value (if (consp c) (cdr c) nil))
    (cons (if (consp c) (car c) nil)
          (fn-hsr-put (1- i) value (if (consp c) (cdr c) nil)))))

(local
 (defun fn-hsr-put-field-ind (i j c)
   (declare (xargs :measure (nfix i) :verify-guards nil))
   (if (or (zp i) (zp j)) c
     (fn-hsr-put-field-ind (1- i) (1- j) (if (consp c) (cdr c) nil)))))
(local
 (defthm fn-hsr-field-of-put
   (implies (and (natp i) (natp j))
            (equal (fn-hsr-field j (fn-hsr-put i value c))
                   (if (equal i j) value (fn-hsr-field j c))))
   :hints (("Goal" :induct (fn-hsr-put-field-ind i j c)
            :expand ((fn-hsr-put i value c)
                     (fn-hsr-field j c)
                     (:free (a b) (fn-hsr-field j (cons a b))))
            :in-theory (enable fn-hsr-put fn-hsr-field)))))

(local
 (defthm fn-hsr-put-preserves-width
   (implies (and (natp i) (natp k) (< i k) (fn-hsr-widthp c k))
            (fn-hsr-widthp (fn-hsr-put i value c) k))
   :hints (("Goal" :induct (fn-hsr-put-field-ind i k c)
            :in-theory (enable fn-hsr-put fn-hsr-widthp)))))

(defun fn-hsr-rootp (root)
  (declare (xargs :guard t))
  (and (fn-hsr-widthp root 6) (equal (fn-hsr-field 0 root) :pgs-commit)
       (unsigned-byte-p 64 (fn-hsr-field 1 root))
       (unsigned-byte-p 64 (fn-hsr-field 2 root))
       (unsigned-byte-p 64 (fn-hsr-field 3 root))
       (unsigned-byte-p 256 (fn-hsr-field 4 root))
       (unsigned-byte-p 256 (fn-hsr-field 5 root))))

(defun fn-hsr-tagp (tag)
  (declare (xargs :guard t))
  (and (fn-hsr-widthp tag 4) (natp (fn-hsr-field 0 tag))
       (natp (fn-hsr-field 1 tag)) (natp (fn-hsr-field 2 tag))
       (member-eq (fn-hsr-field 3 tag) '(:directory :table :data))))

; Fixed19 cells: mode,io,root,logical,physical-base,total-words,word-position,
; word-used,word-acc,<=16u32 block,scan,expected-digest,directory-pages,table-index,
; table-count,borrow-page-start,phase,last-verdict,digest-identity-tag.
(defun fn-hsr-auth-shapep (c)
  (declare (xargs :guard t))
  (and (fn-hsr-widthp c 19)
       (member-eq (fn-hsr-field 0 c)
                  '(:idle :need-read :waiting :digest :byte :release :verified :refused :uncertain))
       (fn-hsr-io-shapep (fn-hsr-field 1 c)) (fn-hsr-rootp (fn-hsr-field 2 c))
       (natp (fn-hsr-field 3 c)) (natp (fn-hsr-field 4 c))
       (natp (fn-hsr-field 5 c)) (natp (fn-hsr-field 6 c))
       (fn-hrcur-wordp (fn-hsr-field 7 c) (fn-hsr-field 8 c))
       (fn-hsr-prefixp (fn-hsr-field 9 c) 16)
       (or (not (fn-hsr-field 10 c)) (fn-hsr-scan-shapep (fn-hsr-field 10 c)))
       (unsigned-byte-p 256 (fn-hsr-field 11 c))
       (natp (fn-hsr-field 12 c)) (natp (fn-hsr-field 13 c))
       (natp (fn-hsr-field 14 c)) (natp (fn-hsr-field 15 c))
       (member-eq (fn-hsr-field 16 c) '(:directory :table :data))
       (fn-hsr-tagp (fn-hsr-field 18 c))))

; Logical lifetime coupling; never evaluated by a runtime guard.
(defun fn-hsr-auth-lifetimep (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-hsr-auth-shapep c) (fn-hsr-io-invariantp (fn-hsr-field 1 c))
       (let ((mode (fn-hsr-field 0 c)) (iomode (fn-hsr-field 0 (fn-hsr-field 1 c))))
         (and (implies (member-eq mode '(:idle :need-read)) (equal iomode :idle))
              (implies (equal mode :waiting) (equal iomode :waiting))
              (implies (member-eq mode '(:digest :byte :release :verified)) (equal iomode :observed))
              (implies (equal mode :uncertain) (equal iomode :uncertain))))))

(local
 (defthm fn-hsr-io-invariant-implies-shape
   (implies (fn-hsr-io-invariantp c) (fn-hsr-io-shapep c))
   :hints (("Goal" :in-theory (e/d (fn-hsr-io-invariantp)
                                  (fn-hsr-io-shapep fn-hsr-field))))))

(defun fn-hsr-auth-begin (root ticket epoch capture lease)
  ; ROOT is the captured selected checkpoint F binding, not bytes from page0.
  ; Root selection/self-check and physical incarnation pinning precede BEGIN.
  (declare (xargs :guard t))
  (if (not (and (fn-hsr-rootp root) (natp ticket) (natp epoch)))
      (mv '(:refused :root-shape) nil)
    (let* ((np (fn-hsr-field 3 root)) (nt (pgs-x-ntables np))
           (m (pgs-ptab-run-pages nt)))
      (if (not (< m 4294967296)) (mv '(:refused :directory-domain) nil)
        (mv :idle
            (list :idle (fn-hsr-io-begin ticket epoch capture lease) root 0 0 0 0
                  0 0 nil nil 0 m 0 0 0 :directory nil
                  (list ticket epoch 0 :directory)))))))

; Initial carried shape includes the pending/borrow lifetime invariant.
(defthm fn-hsr-auth-begin-establishes-shape
  (implies (equal (mv-nth 0 (fn-hsr-auth-begin root ticket epoch capture lease)) :idle)
           (and (fn-hsr-auth-shapep (mv-nth 1 (fn-hsr-auth-begin root ticket epoch capture lease)))
                (fn-hsr-io-invariantp
                 (fn-hsr-field 1 (mv-nth 1 (fn-hsr-auth-begin root ticket epoch capture lease))))))
  :hints (("Goal" :in-theory
           (enable fn-hsr-auth-begin fn-hsr-auth-shapep fn-hsr-io-begin
                   fn-hsr-io-invariantp fn-hsr-io-shapep fn-hsr-tagp
                   fn-hsr-widthp fn-hsr-field fn-hsr-prefixp fn-hrcur-wordp))))

(defthm fn-hsr-auth-begin-establishes-lifetime
  (implies (equal (mv-nth 0 (fn-hsr-auth-begin root ticket epoch capture lease)) :idle)
           (fn-hsr-auth-lifetimep
            (mv-nth 1 (fn-hsr-auth-begin root ticket epoch capture lease))))
  :hints (("Goal" :use ((:instance fn-hsr-auth-begin-establishes-shape))
           :in-theory
           (e/d (fn-hsr-auth-lifetimep fn-hsr-auth-begin fn-hsr-io-begin fn-hsr-field)
                (fn-hsr-auth-shapep fn-hsr-io-invariantp fn-hsr-auth-begin-establishes-shape)))))

(defun fn-hsr-auth-open-phase (phase physical total count selected expected c pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t))
  (if (not (and (fn-hsr-auth-shapep c) (natp physical) (natp total)
                (equal (mod total 8) 0) (posp total)
                (unsigned-byte-p 256 expected)
                (member-eq phase '(:directory :table :data))
                (or (equal phase :data)
                    (and (unsigned-byte-p 64 count) (unsigned-byte-p 64 selected)
                         (unsigned-byte-p 64 total) (< selected count) (<= (* 6 count) total)))))
      (mv '(:refused :phase-domain) c pgs-digest-state)
    (let* ((io (fn-hsr-field 1 c))
           (tag (list (fn-hsr-field 1 io) (fn-hsr-field 2 io) (fn-hsr-field 3 io) phase))
           (scan (if (equal phase :data) nil
                   (fn-hsr-scan-begin total count selected (fn-hsr-field 1 (fn-hsr-field 2 c))
                                      tag (fn-hsr-field 1 io))))
           (next (fn-hsr-put 0 (if (natp (fn-hsr-field 5 io)) :release :need-read)
                  (fn-hsr-put 4 physical (fn-hsr-put 5 total (fn-hsr-put 6 0
                  (fn-hsr-put 7 0 (fn-hsr-put 8 0 (fn-hsr-put 9 nil
                  (fn-hsr-put 10 scan (fn-hsr-put 11 expected (fn-hsr-put 15 0
                  (fn-hsr-put 16 phase (fn-hsr-put 17 nil (fn-hsr-put 18 tag c))))))))))))))
           (pgs-digest-state (pgs-dc-begin 0 0 (floor total 8) tag (fn-hsr-field 1 io) pgs-digest-state)))
      (mv :yield next pgs-digest-state))))

(defun fn-hsr-auth-select-page (logical c pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t))
  (if (not (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :idle)
                (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :idle)
                (natp logical) (< logical (fn-hsr-field 3 (fn-hsr-field 2 c)))))
      (mv '(:refused :logical-page) c pgs-digest-state)
    (let* ((root (fn-hsr-field 2 c)) (np (fn-hsr-field 3 root))
           (tp (pgs-tq logical)) (count (min 341 (- np (* 341 tp))))
           (next (fn-hsr-put 3 logical (fn-hsr-put 13 tp (fn-hsr-put 14 (nfix count) c)))))
      (fn-hsr-auth-open-phase :directory (fn-hsr-field 2 root) (* 2048 (fn-hsr-field 12 c))
                              (pgs-x-ntables np) tp (fn-hsr-field 4 root) next pgs-digest-state))))

(defun fn-hsr-auth-request (c)
  (declare (xargs :guard t))
  (if (not (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :need-read)
                (equal (mod (fn-hsr-field 6 c) 2048) 0)
                (< (fn-hsr-field 6 c) (fn-hsr-field 5 c))
                (equal (fn-hsr-field 7 c) 0) (not (fn-hsr-field 9 c))))
      (mv '(:refused :request-state) nil c)
    (mv-let (verdict request io)
      (fn-hsr-io-request (fn-hsr-field 16 c)
                         (+ (fn-hsr-field 4 c) (floor (fn-hsr-field 6 c) 2048))
                         (fn-hsr-field 3 c) (fn-hsr-field 1 c))
      (mv verdict request
          (if (equal verdict :need-read)
              (fn-hsr-put 0 :waiting (fn-hsr-put 1 io c)) c)))))

(local
 (defthm fn-hsr-io-request-shape
   (implies (fn-hsr-io-shapep c)
            (fn-hsr-io-shapep (mv-nth 2 (fn-hsr-io-request phase physical logical c))))
   :hints (("Goal" :in-theory
            (enable fn-hsr-io-request fn-hsr-io-shapep fn-hsr-io-requestp
                    fn-hsr-field fn-hsr-widthp)))))

(defthm fn-hsr-auth-request-preserves-shape
  (implies (fn-hsr-auth-shapep c)
           (fn-hsr-auth-shapep (mv-nth 2 (fn-hsr-auth-request c))))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-request fn-hsr-auth-shapep)
                (fn-hsr-put fn-hsr-field fn-hsr-io-request fn-hsr-io-shapep
                 fn-hsr-rootp fn-hsr-tagp fn-hsr-prefixp fn-hrcur-wordp
                 fn-hsr-scan-shapep floor mod)))))

(defthm fn-hsr-auth-request-preserves-lifetime
  (implies (fn-hsr-auth-lifetimep c)
           (fn-hsr-auth-lifetimep (mv-nth 2 (fn-hsr-auth-request c))))
  :hints (("Goal" :use
           ((:instance fn-hsr-auth-request-preserves-shape)
            (:instance fn-hsr-io-request-preserves-invariant
             (c (fn-hsr-field 1 c)) (phase (fn-hsr-field 16 c))
             (physical (+ (fn-hsr-field 4 c) (floor (fn-hsr-field 6 c) 2048)))
             (logical (fn-hsr-field 3 c))))
           :in-theory
           (e/d (fn-hsr-auth-lifetimep fn-hsr-auth-request fn-hsr-io-request fn-hsr-field)
                (fn-hsr-put fn-hsr-auth-shapep fn-hsr-io-shapep fn-hsr-io-invariantp
                 floor mod fn-hsr-auth-request-preserves-shape
                 fn-hsr-io-request-preserves-invariant)))))

(local
 (defthm fn-hsr-io-waiting-completion-shape-and-mode
   (implies (and (fn-hsr-io-shapep c) (equal (fn-hsr-field 0 c) :waiting))
            (let* ((completed (fn-hsr-io-complete request discovery-id count status c))
                   (v (mv-nth 0 completed)) (next (mv-nth 1 completed)))
              (and (fn-hsr-io-shapep next)
                   (member-eq (fn-hsr-field 0 next) '(:waiting :observed :refused :uncertain))
                   (equal (equal (fn-hsr-field 0 next) :observed) (equal v :observed)))))
   :hints (("Goal" :in-theory
            (enable fn-hsr-io-complete fn-hsr-io-shapep fn-hsr-field fn-hsr-widthp)))))

(defun fn-hsr-auth-complete (request discovery-id count status c)
  (declare (xargs :guard t))
  (if (not (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :waiting)
                (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :waiting)))
      (mv '(:refused :completion-state) c)
    (mv-let (verdict io)
      (fn-hsr-io-complete request discovery-id count status (fn-hsr-field 1 c))
      (cond ((equal verdict :observed)
             (mv :yield (fn-hsr-put 0 :digest (fn-hsr-put 1 io
                         (fn-hsr-put 15 (fn-hsr-field 6 c) c)))))
            ((equal (fn-hsr-field 0 io) :waiting) (mv verdict c))
            (t (mv verdict (fn-hsr-put 0 (fn-hsr-field 0 io)
                            (fn-hsr-put 1 io (fn-hsr-put 17 verdict c)))))))))

(defthm fn-hsr-auth-complete-preserves-shape
  (implies (fn-hsr-auth-shapep c)
           (fn-hsr-auth-shapep (mv-nth 1 (fn-hsr-auth-complete request discovery-id count status c))))
  :hints (("Goal" :use
           ((:instance fn-hsr-io-waiting-completion-shape-and-mode (c (fn-hsr-field 1 c))))
           :in-theory
           (e/d (fn-hsr-auth-complete fn-hsr-auth-shapep)
                (fn-hsr-put fn-hsr-field fn-hsr-io-complete fn-hsr-io-shapep
                 fn-hsr-rootp fn-hsr-tagp fn-hsr-prefixp fn-hrcur-wordp fn-hsr-scan-shapep
                 fn-hsr-io-waiting-completion-shape-and-mode)))))

(defthm fn-hsr-auth-complete-preserves-lifetime
  (implies (fn-hsr-auth-lifetimep c)
           (fn-hsr-auth-lifetimep
            (mv-nth 1 (fn-hsr-auth-complete request discovery-id count status c))))
  :hints (("Goal" :use
           ((:instance fn-hsr-auth-complete-preserves-shape)
            (:instance fn-hsr-io-complete-preserves-invariant (c (fn-hsr-field 1 c)))
            (:instance fn-hsr-io-waiting-completion-shape-and-mode (c (fn-hsr-field 1 c))))
           :in-theory
           (e/d (fn-hsr-auth-lifetimep fn-hsr-auth-complete)
                (fn-hsr-put fn-hsr-field fn-hsr-auth-shapep fn-hsr-io-shapep fn-hsr-io-invariantp
                 fn-hsr-io-complete fn-hsr-io-waiting-completion-shape-and-mode
                 fn-hsr-auth-complete-preserves-shape fn-hsr-io-complete-preserves-invariant)))))

(defun fn-hsr-auth-byte-demand (c)
  (declare (xargs :guard t))
  (if (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :byte)
           (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :observed)
           (natp (fn-hsr-field 5 (fn-hsr-field 1 c))))
      (list :buffer-byte (fn-hsr-field 5 (fn-hsr-field 1 c))
            (mod (+ (* 8 (fn-hsr-field 6 c)) (fn-hsr-field 7 c)) 16384) 1)
    nil))

(defun fn-hsr-auth-refuse (reason c)
  (declare (xargs :guard t))
  (mv (list :refused reason)
      (fn-hsr-put 0 :refused (fn-hsr-put 17 (list :refused reason) c))))

(local
 (defthm fn-hsr-block-is-true-list
   (implies (fn-hsr-prefixp block k) (true-listp block))))

(defun fn-hsr-auth-feed-byte (discovery-id offset byte c)
  (declare (xargs :guard t))
  (if (not (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :byte)
                (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :observed)
                (natp discovery-id) (equal discovery-id (fn-hsr-field 5 (fn-hsr-field 1 c)))
                (equal offset (mod (+ (* 8 (fn-hsr-field 6 c)) (fn-hsr-field 7 c)) 16384))
                (unsigned-byte-p 8 byte) (< (fn-hsr-field 6 c) (fn-hsr-field 5 c))
                (<= (len (fn-hsr-field 9 c)) 14)
                (equal (mod (len (fn-hsr-field 9 c)) 2) 0)))
      (mv '(:refused :byte-coordinate) c)
    (mv-let (verdict word used acc)
      (fn-hrcur-word-push byte (fn-hsr-field 7 c) (fn-hsr-field 8 c))
      (cond ((equal verdict :continue)
             (mv :yield (fn-hsr-put 7 used (fn-hsr-put 8 acc c))))
            ((not (and (equal verdict :emit) (unsigned-byte-p 64 word)))
             (fn-hsr-auth-refuse :word-state c))
            (t
             (mv-let (scan-verdict scan)
               (if (equal (fn-hsr-field 16 c) :data) (mv :continue nil)
                 (fn-hsr-scan-word word (fn-hsr-field 10 c)))
               (if (not (equal scan-verdict :continue)) (fn-hsr-auth-refuse scan-verdict c)
                 (let* ((block (append (fn-hsr-field 9 c) (list (pgs-lo32 word) (pgs-hi32 word))))
                        (next (fn-hsr-put 0 (if (equal (len block) 16) :digest :byte)
                               (fn-hsr-put 6 (+ 1 (fn-hsr-field 6 c))
                               (fn-hsr-put 7 used (fn-hsr-put 8 acc
                               (fn-hsr-put 9 block (fn-hsr-put 10 scan c))))))))
                   (mv :yield next)))))))))

(defun fn-hsr-auth-finish-phase (c pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t))
  (if (not (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :digest)
                (equal (pgs-dc-mode pgs-digest-state) :done)
                (equal (fn-hsr-field 6 c) (fn-hsr-field 5 c))
                (equal (fn-hsr-field 7 c) 0) (not (fn-hsr-field 9 c))))
      (mv-let (verdict next) (fn-hsr-auth-refuse :phase-incomplete c)
        (mv verdict next pgs-digest-state))
    (let* ((phase (fn-hsr-field 16 c)) (scan (fn-hsr-field 10 c))
           (entry (if (equal phase :data) nil (fn-hsr-scan-entry scan)))
           (complete (or (equal phase :data)
                         (and (fn-hsr-scan-shapep scan)
                              (equal (fn-hsr-field 0 scan) (fn-hsr-field 5 c))
                              (fn-hsr-widthp entry 3)
                              (unsigned-byte-p 64 (fn-hsr-field 0 entry))
                              (unsigned-byte-p 256 (fn-hsr-field 2 entry)))))
           (bad (and (not (equal phase :data)) (fn-hsr-field 6 scan)))
           (verdict (fn-hsr-page-verdict phase
                     (if (equal phase :table) (fn-hsr-field 13 c) (fn-hsr-field 3 c))
                     (fn-hsr-field 4 c) (fn-hsr-field 11 c) (pgs-dc-result pgs-digest-state) bad)))
      (cond ((not complete)
             (mv-let (v next) (fn-hsr-auth-refuse :entry-incomplete c) (mv v next pgs-digest-state)))
            (verdict
             (mv-let (v next) (fn-hsr-auth-refuse verdict c) (mv v next pgs-digest-state)))
            ((equal phase :directory)
             (fn-hsr-auth-open-phase :table (fn-hsr-field 0 entry) 2048
                                     (fn-hsr-field 14 c) (pgs-tr (fn-hsr-field 3 c))
                                     (fn-hsr-field 2 entry) c pgs-digest-state))
            ((equal phase :table)
             (fn-hsr-auth-open-phase :data (fn-hsr-field 0 entry) 2048 0 0
                                     (fn-hsr-field 2 entry) c pgs-digest-state))
            (t (let* ((io (fn-hsr-field 1 c))
                      (result (list :verified-page (fn-hsr-field 1 io) (fn-hsr-field 2 io)
                                    (fn-hsr-field 3 c) (fn-hsr-field 4 c) (fn-hsr-field 5 io))))
                 (mv result (fn-hsr-put 0 :verified (fn-hsr-put 17 result c)) pgs-digest-state)))))))

(defun fn-hsr-auth-digest-tick (c pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard t
                  :guard-hints (("Goal" :in-theory (enable pgs-dc-next-word-offset)))))
  (if (not (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :digest)
                (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :observed)
                (natp (fn-hsr-field 5 (fn-hsr-field 1 c)))
                (equal (pgs-dc-capture pgs-digest-state) (fn-hsr-field 18 c))
                (equal (pgs-dc-lease pgs-digest-state) (fn-hsr-field 1 (fn-hsr-field 1 c)))
                (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
                (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
                (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))))
      (mv-let (v next) (fn-hsr-auth-refuse :digest-state c) (mv v next pgs-digest-state))
    (let* ((needs (pgs-dc-needs-block pgs-digest-state)) (block (fn-hsr-field 9 c))
           (pos (fn-hsr-field 6 c)) (offset (pgs-dc-next-word-offset pgs-digest-state)))
      (cond
       ((and needs (not block))
        (if (not (and (equal pos offset) (equal (pgs-dc-read-demand pgs-digest-state) 8)
                      (< pos (fn-hsr-field 5 c)) (equal (fn-hsr-field 7 c) 0)))
            (mv-let (v next) (fn-hsr-auth-refuse :digest-coordinate c) (mv v next pgs-digest-state))
          (mv :yield (fn-hsr-put 0 (if (<= (+ 2048 (fn-hsr-field 15 c)) pos) :release :byte) c)
              pgs-digest-state)))
       ((and needs (not (and (equal (len block) 16) (equal pos (+ 8 offset)))))
        (mv-let (v next) (fn-hsr-auth-refuse :digest-block c) (mv v next pgs-digest-state)))
       ((and (not needs) block)
        (mv-let (v next) (fn-hsr-auth-refuse :unexpected-block c) (mv v next pgs-digest-state)))
       (t
        (mv-let (verdict pgs-digest-state) (pgs-dc-step (if needs block nil) pgs-digest-state)
          (let ((next (fn-hsr-put 9 nil c)))
            (cond ((equal verdict :done) (fn-hsr-auth-finish-phase next pgs-digest-state))
                  ((equal verdict :continue) (mv :yield next pgs-digest-state))
                  (t (mv-let (v next) (fn-hsr-auth-refuse :digest-invalid next)
                       (mv v next pgs-digest-state)))))))))))

(local
 (defthm fn-hsr-io-release-shape
   (implies (fn-hsr-io-shapep c)
            (fn-hsr-io-shapep (mv-nth 1 (fn-hsr-io-release discovery-id c))))
   :hints (("Goal" :in-theory
            (enable fn-hsr-io-release fn-hsr-io-shapep fn-hsr-field fn-hsr-widthp)))))

(defun fn-hsr-auth-release (discovery-id c)
  (declare (xargs :guard t))
  (if (not (and (fn-hsr-auth-shapep c)
                (member-eq (fn-hsr-field 0 c) '(:release :verified :refused :uncertain))))
      (mv '(:refused :release-state) c)
    (mv-let (verdict io) (fn-hsr-io-release discovery-id (fn-hsr-field 1 c))
      (if (not (equal verdict :released)) (mv verdict c)
        (mv :released
            (fn-hsr-put 0 (cond ((equal (fn-hsr-field 0 c) :release) :need-read)
                                ((equal (fn-hsr-field 0 c) :verified) :idle)
                                (t (fn-hsr-field 0 c)))
                         (fn-hsr-put 1 io c)))))))

(defthm fn-hsr-auth-release-preserves-shape
  (implies (fn-hsr-auth-shapep c)
           (fn-hsr-auth-shapep (mv-nth 1 (fn-hsr-auth-release discovery-id c))))
  :hints (("Goal" :in-theory (e/d (fn-hsr-auth-release fn-hsr-auth-shapep)
                (fn-hsr-io-release fn-hsr-io-shapep fn-hsr-field fn-hsr-put fn-hsr-rootp fn-hsr-tagp
                 fn-hsr-prefixp fn-hsr-scan-shapep fn-hrcur-wordp)))))

(defthm fn-hsr-auth-release-preserves-lifetime
  (implies (fn-hsr-auth-lifetimep c)
           (fn-hsr-auth-lifetimep (mv-nth 1 (fn-hsr-auth-release discovery-id c))))
  :hints (("Goal" :use
           ((:instance fn-hsr-auth-release-preserves-shape)
            (:instance fn-hsr-io-release-preserves-invariant (c (fn-hsr-field 1 c))))
           :in-theory
           (e/d (fn-hsr-auth-lifetimep fn-hsr-auth-release fn-hsr-io-release fn-hsr-field)
                (fn-hsr-put fn-hsr-auth-shapep fn-hsr-io-shapep fn-hsr-io-invariantp
                 fn-hsr-auth-release-preserves-shape fn-hsr-io-release-preserves-invariant)))))

(local
 (defthm fn-hsr-io-cancel-shape
   (implies (fn-hsr-io-shapep c)
            (fn-hsr-io-shapep (mv-nth 1 (fn-hsr-io-cancel c))))
   :hints (("Goal" :in-theory
            (enable fn-hsr-io-cancel fn-hsr-io-shapep fn-hsr-field fn-hsr-widthp)))))

(defun fn-hsr-auth-cancel (c)
  (declare (xargs :guard t))
  (if (not (fn-hsr-auth-shapep c)) (mv '(:refused :cancel-state) c)
    (mv-let (verdict io) (fn-hsr-io-cancel (fn-hsr-field 1 c))
      (mv verdict (fn-hsr-put 0 (cond ((equal (fn-hsr-field 0 io) :waiting) :waiting)
                                     ((equal (fn-hsr-field 0 c) :uncertain) :uncertain)
                                     ((equal (fn-hsr-field 0 io) :uncertain) :uncertain)
                                     (t :refused))
                              (fn-hsr-put 1 io (fn-hsr-put 17 verdict c)))))))

(defthm fn-hsr-auth-cancel-preserves-shape
  (implies (fn-hsr-auth-shapep c)
           (fn-hsr-auth-shapep (mv-nth 1 (fn-hsr-auth-cancel c))))
  :hints (("Goal" :in-theory (e/d (fn-hsr-auth-cancel fn-hsr-auth-shapep)
                (fn-hsr-io-cancel fn-hsr-io-shapep fn-hsr-field fn-hsr-put fn-hsr-rootp fn-hsr-tagp
                 fn-hsr-prefixp fn-hsr-scan-shapep fn-hrcur-wordp)))))

(defthm fn-hsr-auth-cancel-preserves-lifetime
  (implies (fn-hsr-auth-lifetimep c)
           (fn-hsr-auth-lifetimep (mv-nth 1 (fn-hsr-auth-cancel c))))
  :hints (("Goal" :use
           ((:instance fn-hsr-auth-cancel-preserves-shape)
            (:instance fn-hsr-io-cancel-preserves-invariant (c (fn-hsr-field 1 c))))
           :in-theory
           (e/d (fn-hsr-auth-lifetimep fn-hsr-auth-cancel fn-hsr-io-cancel fn-hsr-field)
                (fn-hsr-put fn-hsr-auth-shapep fn-hsr-io-shapep fn-hsr-io-invariantp
                 fn-hsr-auth-cancel-preserves-shape fn-hsr-io-cancel-preserves-invariant)))))

(defun fn-hsr-auth-joined-failure (request outcome c)
  (declare (xargs :guard t))
  (if (not (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :waiting)
                (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :waiting)))
      (mv '(:refused :join-state) c)
    (mv-let (verdict io) (fn-hsr-io-joined-failure request outcome (fn-hsr-field 1 c))
      (if (equal (fn-hsr-field 0 io) :waiting) (mv verdict c)
        (mv verdict (fn-hsr-put 0 (fn-hsr-field 0 io)
                                (fn-hsr-put 1 io (fn-hsr-put 17 verdict c))))))))

(defthm fn-hsr-auth-joined-failure-preserves-shape
  (implies (fn-hsr-auth-shapep c)
           (fn-hsr-auth-shapep (mv-nth 1 (fn-hsr-auth-joined-failure request outcome c))))
  :hints (("Goal" :in-theory (e/d (fn-hsr-auth-joined-failure fn-hsr-auth-shapep fn-hsr-io-joined-failure fn-hsr-io-shapep fn-hsr-field fn-hsr-widthp)
                (fn-hsr-put fn-hsr-rootp fn-hsr-tagp
                 fn-hsr-prefixp fn-hsr-scan-shapep fn-hrcur-wordp)))))

(defthm fn-hsr-auth-joined-failure-preserves-lifetime
  (implies (fn-hsr-auth-lifetimep c)
           (fn-hsr-auth-lifetimep (mv-nth 1 (fn-hsr-auth-joined-failure request outcome c))))
  :hints (("Goal" :use
           ((:instance fn-hsr-auth-joined-failure-preserves-shape)
            (:instance fn-hsr-io-joined-failure-preserves-invariant (c (fn-hsr-field 1 c))))
           :in-theory
           (e/d (fn-hsr-auth-lifetimep fn-hsr-auth-joined-failure fn-hsr-io-joined-failure fn-hsr-field)
                (fn-hsr-put fn-hsr-auth-shapep fn-hsr-io-shapep fn-hsr-io-invariantp
                 fn-hsr-auth-joined-failure-preserves-shape fn-hsr-io-joined-failure-preserves-invariant)))))

(defun fn-hsr-auth-verified-byte-demand (offset c)
  (declare (xargs :guard t))
  (if (and (fn-hsr-auth-shapep c) (equal (fn-hsr-field 0 c) :verified)
           (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :observed)
           (natp (fn-hsr-field 5 (fn-hsr-field 1 c)))
           (natp offset) (< offset 16384))
      (list :buffer-byte (fn-hsr-field 5 (fn-hsr-field 1 c)) offset 1)
    nil))

; A short synchronous read is uncertainty, and its returned borrow remains owned.
(defthm fn-hsr-auth-short-completion-retains-borrow
  (implies (and (fn-hsr-auth-shapep c)
                (equal (fn-hsr-field 0 c) :waiting)
                (equal (fn-hsr-field 0 (fn-hsr-field 1 c)) :waiting)
                (equal request (fn-hsr-field 4 (fn-hsr-field 1 c)))
                (natp discovery-id) (not (equal count 16384)))
           (let ((next (mv-nth 1 (fn-hsr-auth-complete request discovery-id count :read-ok c))))
             (and (equal (mv-nth 0 (fn-hsr-auth-complete request discovery-id count :read-ok c))
                         '(:uncertain :read-completion))
                  (equal (fn-hsr-field 0 next) :uncertain)
                  (equal (fn-hsr-field 5 (fn-hsr-field 1 next)) discovery-id)
                  (equal (fn-hsr-field 2 next) (fn-hsr-field 2 c))
                  (not (fn-hsr-auth-byte-demand next))
                  (not (fn-hsr-auth-verified-byte-demand 0 next)))))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-complete fn-hsr-io-complete fn-hsr-auth-shapep
                 fn-hsr-auth-byte-demand fn-hsr-auth-verified-byte-demand fn-hsr-field)
                (fn-hsr-io-shapep fn-hsr-put fn-hsr-rootp fn-hsr-prefixp
                 fn-hsr-widthp fn-hsr-tagp fn-hrcur-wordp fn-hsr-scan-shapep)))))

; Fixed selected root, root ticket, epoch and opaque source/lease projection.
(defun fn-hsr-auth-identities (c)
  (declare (xargs :guard t))
  (list (fn-hsr-field 2 c) (fn-hsr-io-identities (fn-hsr-field 1 c))))

(local
 (encapsulate ()
(defthm fn-hsr-auth-open-phase-preserves-identities
  (equal (fn-hsr-auth-identities
          (mv-nth 1 (fn-hsr-auth-open-phase phase physical total count selected expected c pgs-digest-state)))
         (fn-hsr-auth-identities c))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-identities fn-hsr-auth-open-phase)
                (fn-hsr-put fn-hsr-field fn-hsr-auth-shapep pgs-dc-begin fn-hsr-io-identities)))))

(defthm fn-hsr-auth-refuse-preserves-identities
  (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-refuse reason c)))
         (fn-hsr-auth-identities c))
  :hints (("Goal" :in-theory (e/d (fn-hsr-auth-identities fn-hsr-auth-refuse)
                                  (fn-hsr-put fn-hsr-field fn-hsr-io-identities)))))
(defthm fn-hsr-auth-select-page-preserves-identities
  (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-select-page logical c pgs-digest-state)))
         (fn-hsr-auth-identities c))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-select-page fn-hsr-auth-identities)
                (fn-hsr-put fn-hsr-field fn-hsr-auth-shapep fn-hsr-io-identities
                 fn-hsr-auth-open-phase fn-hsr-auth-refuse fn-hsr-io-request
                 fn-hsr-io-complete fn-hsr-io-release fn-hsr-io-cancel fn-hsr-io-joined-failure
                 fn-hsr-scan-word fn-hrcur-word-push)))))

(defthm fn-hsr-auth-request-preserves-identities
  (equal (fn-hsr-auth-identities (mv-nth 2 (fn-hsr-auth-request c)))
         (fn-hsr-auth-identities c))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-request fn-hsr-auth-identities)
                (fn-hsr-put fn-hsr-field fn-hsr-auth-shapep fn-hsr-io-identities
                 fn-hsr-auth-open-phase fn-hsr-auth-refuse fn-hsr-io-request
                 fn-hsr-io-complete fn-hsr-io-release fn-hsr-io-cancel fn-hsr-io-joined-failure
                 fn-hsr-scan-word fn-hrcur-word-push)))))

(defthm fn-hsr-auth-complete-preserves-identities
  (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-complete request discovery-id count status c)))
         (fn-hsr-auth-identities c))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-complete fn-hsr-auth-identities)
                (fn-hsr-put fn-hsr-field fn-hsr-auth-shapep fn-hsr-io-identities
                 fn-hsr-auth-open-phase fn-hsr-auth-refuse fn-hsr-io-request
                 fn-hsr-io-complete fn-hsr-io-release fn-hsr-io-cancel fn-hsr-io-joined-failure
                 fn-hsr-scan-word fn-hrcur-word-push)))))

(defthm fn-hsr-auth-feed-byte-preserves-identities
  (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-feed-byte discovery-id offset byte c)))
         (fn-hsr-auth-identities c))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-feed-byte fn-hsr-auth-identities)
                (fn-hsr-put fn-hsr-field fn-hsr-auth-shapep fn-hsr-io-identities
                 fn-hsr-auth-open-phase fn-hsr-auth-refuse fn-hsr-io-request
                 fn-hsr-io-complete fn-hsr-io-release fn-hsr-io-cancel fn-hsr-io-joined-failure
                 fn-hsr-scan-word fn-hrcur-word-push)))))

(defthm fn-hsr-auth-release-preserves-identities
  (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-release discovery-id c)))
         (fn-hsr-auth-identities c))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-release fn-hsr-auth-identities)
                (fn-hsr-put fn-hsr-field fn-hsr-auth-shapep fn-hsr-io-identities
                 fn-hsr-auth-open-phase fn-hsr-auth-refuse fn-hsr-io-request
                 fn-hsr-io-complete fn-hsr-io-release fn-hsr-io-cancel fn-hsr-io-joined-failure
                 fn-hsr-scan-word fn-hrcur-word-push)))))

(defthm fn-hsr-auth-cancel-preserves-identities
  (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-cancel c)))
         (fn-hsr-auth-identities c))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-cancel fn-hsr-auth-identities)
                (fn-hsr-put fn-hsr-field fn-hsr-auth-shapep fn-hsr-io-identities
                 fn-hsr-auth-open-phase fn-hsr-auth-refuse fn-hsr-io-request
                 fn-hsr-io-complete fn-hsr-io-release fn-hsr-io-cancel fn-hsr-io-joined-failure
                 fn-hsr-scan-word fn-hrcur-word-push)))))

(defthm fn-hsr-auth-joined-failure-preserves-identities
  (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-joined-failure request outcome c)))
         (fn-hsr-auth-identities c))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-joined-failure fn-hsr-auth-identities)
                (fn-hsr-put fn-hsr-field fn-hsr-auth-shapep fn-hsr-io-identities
                 fn-hsr-auth-open-phase fn-hsr-auth-refuse fn-hsr-io-request
                 fn-hsr-io-complete fn-hsr-io-release fn-hsr-io-cancel fn-hsr-io-joined-failure
                 fn-hsr-scan-word fn-hrcur-word-push)))))

(defthm fn-hsr-auth-finish-phase-preserves-identities
  (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-finish-phase c pgs-digest-state)))
         (fn-hsr-auth-identities c))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-finish-phase fn-hsr-auth-identities)
                (fn-hsr-put fn-hsr-field fn-hsr-auth-shapep fn-hsr-io-identities
                 fn-hsr-auth-open-phase fn-hsr-auth-refuse fn-hsr-scan-entry
                 fn-hsr-page-verdict pgs-dc-result)))))

(defthm fn-hsr-auth-digest-tick-preserves-identities
  (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-digest-tick c pgs-digest-state)))
         (fn-hsr-auth-identities c))
  :hints (("Goal" :in-theory
           (e/d (fn-hsr-auth-digest-tick fn-hsr-auth-identities)
                (fn-hsr-put fn-hsr-field fn-hsr-auth-shapep fn-hsr-io-identities
                 fn-hsr-auth-finish-phase fn-hsr-auth-refuse pgs-dc-step
                 pgs-dc-needs-block pgs-dc-next-word-offset pgs-dc-read-demand)))))
))

(defthm fn-hsr-auth-transitions-preserve-identities-by-definition
  (and (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-select-page logical c pgs-digest-state)))
                (fn-hsr-auth-identities c))
       (equal (fn-hsr-auth-identities (mv-nth 2 (fn-hsr-auth-request c)))
                (fn-hsr-auth-identities c))
       (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-complete request discovery-id count status c)))
                (fn-hsr-auth-identities c))
       (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-feed-byte discovery-id offset byte c)))
                (fn-hsr-auth-identities c))
       (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-digest-tick c pgs-digest-state)))
                (fn-hsr-auth-identities c))
       (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-release discovery-id c)))
                (fn-hsr-auth-identities c))
       (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-cancel c)))
                (fn-hsr-auth-identities c))
       (equal (fn-hsr-auth-identities (mv-nth 1 (fn-hsr-auth-joined-failure request outcome c)))
                (fn-hsr-auth-identities c)))
  :hints (("Goal" :in-theory (disable fn-hsr-auth-identities fn-hsr-auth-select-page fn-hsr-auth-request fn-hsr-auth-complete fn-hsr-auth-feed-byte fn-hsr-auth-digest-tick fn-hsr-auth-release fn-hsr-auth-cancel fn-hsr-auth-joined-failure))))
