;;; host/native/spike-storage.lisp -- spike/storage (D28).  Native host side of
;;; the storage-at-scale spike.  Loaded last by host/native/build.lisp.  Every
;;; decision the host makes here that ACL2 should own is marked SPIKE; the
;;; record is planning/evidence/spike-storage-2026-09-25.md.
(in-package "ACL2")

(require :sb-sprof)

;;; ---------------------------------------------------------------------------
;;; B. Developer profiling: FN_SPIKE_SPROF=PATH wraps the dispatch in the
;;; statistical profiler and writes the flat report to PATH at the end.
;;; SPIKE: a diagnostic only; it changes no outcome.

(defvar *fnn-spk-dispatch* #'fnn-dispatch)

(defun fnn-dispatch (args)
  (let ((path (sb-posix:getenv "FN_SPIKE_SPROF")))
    (if (and path (plusp (length path)))
        (let ((code nil))
          (sb-sprof:start-profiling :max-samples 400000 :mode :cpu
                                    :sample-interval 0.005 :threads :all)
          (unwind-protect (setq code (funcall *fnn-spk-dispatch* args))
            (sb-sprof:stop-profiling)
            (with-open-file (out path :direction :output :if-exists :supersede)
              (let ((*standard-output* out))
                (sb-sprof:report :type :flat :max 60)
                (sb-sprof:report :type :graph :max 25))))
          code)
        (funcall *fnn-spk-dispatch* args))))

;;; A sealed file: prefix then the ACL2 trailer over it (fnn-seal).
;;; SPIKE: the host compares the recomputed trailer; dev's link reader is an
;;; ACL2 decode over (octets, digest) like fn-store-checkpoint-compaction-*.
(defun fnn-spk-unseal (raw)
  (let* ((tl (fnn-constant :trailer)) (n (length raw)))
    (when (< n tl) (fnn-fault "sealed file is shorter than its trailer"))
    (let ((prefix (subseq raw 0 (- n tl))))
      (unless (equalp (fnn-trailer prefix) (subseq raw (- n tl)))
        (fnn-fault "sealed file trailer mismatch"))
      prefix)))

;;; ---------------------------------------------------------------------------
;;; E. BP journal generation cleanup, called by fnn-bps-open once the service
;;; holds the journal locks and has read the durable selection.

(defun fnn-spk-remove-tree (path depth)
  "Unlink PATH: a file or symlink directly, a directory after its entries.
Never follows a symlink.  DEPTH bounds the recursion (work, not data)."
  (let ((st (fnn-lstat path)))
    (cond ((null st) 0)
          ((and (fnn-directory-p st) (not (fnn-symlink-p st)))
           (when (<= depth 0) (fnn-fault "BP cleanup: directory nesting exceeds bound at ~a" path))
           (let ((n 0))
             (dolist (name (fnn-list-directory path))
               (incf n (fnn-spk-remove-tree (fnn-join path name) (1- depth))))
             (fnn-fsync-dir path)
             (sb-posix:rmdir path)
             (1+ n)))
          (t (fnn-unlink path) 1))))

(defun fnn-spk-bp-cleanup (root plan)
  "SPIKE: host-driven removal of the generation directories ACL2's plan
(fn-spk-bp-cleanup-plan) names.  Each unlink and rmdir is a crash cut; a
partial removal leaves an unselected directory the next open finishes."
  (let* ((names (fnn-list-directory root))
         (answer (fnn-core 'fn-spk-bp-cleanup-plan names plan))
         (old (first answer)) (later (second answer)) (strays (third answer))
         (removed 0) (kept nil))
    (dolist (name strays)
      (let ((p (fnn-join root name)))
        (when (fnn-check-regular p) (fnn-unlink p) (incf removed))))
    (dolist (name old)
      (incf removed (fnn-spk-remove-tree (fnn-join root name) 4)))
    (dolist (name later)
      (let ((p (fnn-join root name)))
        (if (null (fnn-list-directory p))
            (progn (sb-posix:rmdir p) (incf removed))
            (push name kept))))
    (when (or old strays later)
      (fnn-fsync-dir root)
      (fnn-out "BP journal cleanup generations=~d strays=~d removed-entries=~d kept-nonempty=~d"
               (length old) (length strays) removed (length kept)))
    removed))

;;; ---------------------------------------------------------------------------
;;; Commands: `--fn spike-store ROOT COMMAND ARGS...' (both images).
;;;   release MSGID... | release --oldest K     one :release per held article
;;;   reclaim [--older-than SECONDS] [--verify] [--dry-run]
;;;   compact-chain [--link-events N]           chained packs (P5)
;;;   chain-retire | chain-status | history-digest
;;; SPIKE: the public operator grammar (books/native-operator) is not
;;; extended; these are a registered verb of the spike images.

(defun fnn-spk-now-dtn-seconds ()
  (- (sb-ext:get-time-of-day) 946684800))

(defun fnn-spk-publish-pending (store what)
  "Publish the ACL2-prepared pending record, as fnn-command-post does."
  (let ((record (fnn-bridge-pending-record))
        (sequence (fnn-pending-sequence (fnn-core-state 'fn-store-sn-pending-sequence))))
    (handler-case (fnn-publish store sequence record)
      (fnn-store-indeterminate (e) (error e))
      (fnn-store-error (e)
        (unless (fnn-store-fenced store)
          (setf (fnn-store-fenced store) t)
          (unless (eq (fnn-bridge-known-abort) :aborted)
            (fnn-indeterminate "ACL2 rejected known pre-publication abort of ~a" what)))
        (error e)))
    (fnn-mark-committed store sequence)
    (setf (fnn-store-fenced store) t)
    (fnn-finish store)
    sequence))

(defun fnn-spk-release-dir (store) (fnn-join (fnn-store-root store) "releases"))

(defun fnn-spk-lp (octets) (append (fnn-core 'fn-spk-u32 (length octets)) octets))

(defun fnn-spk-release-one (store msgid-octets)
  "Write one sealed release record (SPIKE side namespace, see C2)."
  (let ((event (fnn-core-state 'fn-spk-release-event msgid-octets)))
    (unless (consp event) (return-from fnn-spk-release-one event))
    (let* ((dir (fnn-spk-release-dir store))
           (name (format nil "~a.fnrl" (fnn-hex (fnn-octets (fnn-core 'fn-frame-digest (second event))))))
           (final (fnn-join dir name))
           (payload (append (list 70 78 82 76 1) (fnn-spk-lp msgid-octets)
                            (fnn-spk-lp (second event)) (fnn-spk-lp (third event))
                            (fnn-spk-lp (fourth event)) (fnn-core 'fn-spk-u64 (fnn-spk-now-dtn-seconds))))
           (stage (fnn-join (fnn-staging store) (format nil ".stage-release-~d-~a" (sb-posix:getpid) (fnn-random-hex 12)))))
      (fnn-safe-directory dir t)
      (when (fnn-lstat final) (return-from fnn-spk-release-one :already-released))
      (fnn-write-staged stage (fnn-seal (fnn-octets payload)))
      (fnn-link stage final)
      (ignore-errors (fnn-unlink stage))
      :released)))

(defun fnn-spk-released-ids (store)
  "The obligation ids every release record names."
  (let ((dir (fnn-spk-release-dir store)))
    (if (not (fnn-lstat dir)) nil
        (loop for name in (fnn-list-directory dir)
              when (and (> (length name) 5) (string= (subseq name (- (length name) 5)) ".fnrl"))
                collect (let* ((x (fnn-octet-list (fnn-spk-unseal (fnn-read-regular-bounded (fnn-join dir name) 65536))))
                               (y (nthcdr 5 x))
                               (n1 (fnn-core 'fn-spk-get-uint y 4 0))
                               (z (nthcdr (+ 4 n1) y))
                               (n2 (fnn-core 'fn-spk-get-uint z 4 0)))
                          (subseq z 4 (+ 4 n2)))))))

(defun fnn-spk-release (root args)
  (let ((store (fnn-open-live-store root t)) (counts nil))
    (unwind-protect
         (let* ((t0 (get-internal-real-time))
                (msgids (if (and args (string= (first args) "--oldest"))
                            (fnn-core-state 'fn-spk-oldest-held (parse-integer (second args))
                                           (fnn-spk-released-ids store))
                            (mapcar #'fnn-ascii-octet-list args))))
           (dolist (m msgids)
             (let* ((r (fnn-spk-release-one store m)) (p (assoc r counts)))
               (if p (incf (cdr p)) (push (cons r 1) counts))))
           (when (fnn-lstat (fnn-spk-release-dir store))
             (fnn-fsync-dir (fnn-spk-release-dir store))
             (fnn-fsync-dir (fnn-store-root store)))
           (fnn-out "released ~{~(~a~)=~d~^ ~} wall-ms=~d ~a"
                    (loop for (k . v) in counts append (list k v))
                    (round (* 1000 (- (get-internal-real-time) t0))
                           internal-time-units-per-second)
                    (fnn-open-report store))
           +fnn-exit-ok+)
      (fnn-store-close store))))

;;; Rewrite one transaction file in place: stage, fsync, rename over, fsync
;;; the directory.  A crash leaves the old or the new file (rename), and both
;;; open: the stub record replays to the same decisions (SPIKE deferral 1).
(defun fnn-spk-replace-file (store directory final octets tag)
  (let ((stage (fnn-join (fnn-staging store)
                         (format nil ".stage-~a-~d-~a" tag (sb-posix:getpid) (fnn-random-hex 12)))))
    (fnn-write-staged stage octets)
    (fnn-spk-cut (format nil "~a-staged" tag))
    (fnn-replace stage final)
    (fnn-spk-cut (format nil "~a-replaced" tag))
    (fnn-fsync-dir directory)))

(defun fnn-spk-cut (point)
  "Developer cut FN_SPIKE_CUT=POINT: exit 137 at POINT, as a kill would."
  (let ((want (sb-posix:getenv "FN_SPIKE_CUT")))
    (when (and want (string= want point))
      (fnn-out "spike cut at=~a" point) (finish-output)
      (sb-ext:exit :code 137 :abort t))))

(defun fnn-spk-reclaim (root args)
  (let* ((older (let ((p (member "--older-than" args :test #'string=)))
                  (if p (parse-integer (second p)) 0)))
         (verify (member "--verify" args :test #'string=))
         (dry (member "--dry-run" args :test #'string=))
         (t0 (get-internal-real-time)))
    (multiple-value-bind (store records) (fnn-open-live-store root t)
      (declare (ignore records))
      (unwind-protect
           (let* ((t-open (get-internal-real-time))
                  (plan (fnn-core-state 'fn-spk-reclaim-plan (fnn-spk-now-dtn-seconds) older
                                        (fnn-spk-released-ids store))))
             (unless (eq (first plan) :ok)
               (fnn-out "reclaim refused reason=~(~a~)" (second plan))
               (return-from fnn-spk-reclaim +fnn-exit-refused+))
             (let* ((counts (second plan)) (freed (third plan))
                    (eligible (or (cdr (assoc :eligible counts)) 0))
                    (stubbed (fnn-core-state 'fn-spk-reclaim-records))
                    (files 0) (links 0) (cp-before 0) (cp-after 0))
               (fnn-out "reclaim plan ~{~(~a~)=~d~^ ~} payload-octets-freed=~d"
                        (loop for (k . v) in counts append (list k v)) freed)
               (when verify
                 (let ((v (fnn-core-state 'fn-spk-reclaim-verify (fnn-store-frontier store))))
                   (fnn-out "reclaim verify decisions-equal=~(~a~) checkpoint-equals-full=~(~a~) payloads-stubbed=~(~a~) differing-slots=~a event-index-is-stubbed=~(~a~)"
                            (if (first v) t nil) (if (second v) t nil) (if (third v) t nil) (fourth v) (if (fifth v) t nil))))
               (when (or dry (zerop eligible))
                 (fnn-out "reclaim wrote nothing ~a" (fnn-open-report store))
                 (return-from fnn-spk-reclaim +fnn-exit-ok+))
               (setf (fnn-store-fenced store) t)
               ;; 1. The history: suffix files, then chain links.
               (let ((chain-lower (fnn-spk-chain-boundary store)) (by-link nil))
                 (dolist (pair stubbed)
                   (let ((sequence (car pair)) (octets (fnn-octets (cdr pair))))
                     (if (>= sequence chain-lower)
                         (let ((final (fnn-join (fnn-transactions store)
                                                (fnn-transaction-name sequence))))
                           (when (fnn-check-regular final)
                             (fnn-spk-replace-file store (fnn-transactions store) final
                                                   (fnn-frame (fnn-octet-list octets)) "reclaim-record")
                             (incf files)))
                         (push (cons sequence octets) by-link))))
                 (when by-link
                   (setq links (fnn-spk-chain-rebody store (nreverse by-link)))))
               (fnn-spk-cut "reclaim-history-done")
               ;; 2. The checkpoint, after the history it summarizes.
               (let ((path (fnn-state-checkpoint-path store)))
                 (setq cp-before (let ((st (fnn-lstat path))) (if st (sb-posix:stat-size st) 0)))
                 (let* ((segment (fnn-profile-nat 'fn-store-profile-max-record-octets store))
                        (answer (fnn-core-state 'fn-spk-reclaim-checkpoint-octets segment)))
                   (unless (and (consp answer) (fnn-octet-list-p (first answer)))
                     (fnn-fault "ACL2 refused the reclaimed checkpoint"))
                   (fnn-state-checkpoint-write store (fnn-octets (first answer)))
                   (setq cp-after (length (first answer)))))
               (setf (fnn-store-fenced store) nil)
               (fnn-out "reclaim done reclaimed=~d files-rewritten=~d links-rewritten=~d checkpoint-octets=~d->~d open-ms=~d total-ms=~d ~a"
                        eligible files links cp-before cp-after
                        (round (* 1000 (- t-open t0)) internal-time-units-per-second)
                        (round (* 1000 (- (get-internal-real-time) t0)) internal-time-units-per-second)
                        (fnn-open-report store))
               +fnn-exit-ok+))
        (fnn-store-close store)))))

;;; ---------------------------------------------------------------------------
;;; D. Chained packs.  packs-chain/ holds link-GGGGGGGGGGGGGGGGGGGG.fnpl files
;;; and selection.fnps, the sealed u64 pair (generation, header digest) of the
;;; newest link.  SPIKE: the names, the selection frame and the walk are the
;;; host's; the link codec and its checks are ACL2 :program (block D).

(defun fnn-spk-chain-dir (store) (fnn-join (fnn-store-root store) "packs-chain"))
(defun fnn-spk-link-path (store g) (fnn-join (fnn-spk-chain-dir store) (format nil "link-~20,'0d.fnpl" g)))
(defun fnn-spk-chain-selection-path (store) (fnn-join (fnn-spk-chain-dir store) "selection.fnps"))

(defun fnn-spk-chain-selection (store)
  "(GENERATION HEADER-DIGEST) of the selected newest link, or NIL."
  (let ((path (fnn-spk-chain-selection-path store)))
    (when (fnn-check-regular path)
      (let* ((raw (fnn-octet-list (fnn-spk-unseal (fnn-read-regular-bounded path 4096)))))
        (unless (= (length raw) 40) (fnn-fault "chain selection is malformed"))
        (list (fnn-core 'fn-spk-get-uint raw 8 0) (subseq raw 8 40))))))

(defun fnn-spk-read-link (store g)
  (let ((path (fnn-spk-link-path store g)))
    (unless (fnn-check-regular path) (fnn-fault "selected chain link ~d is missing" g))
    (let ((d (fnn-core 'fn-spk-link-decode
                       (fnn-octet-list (fnn-spk-unseal (fnn-read-regular-bounded path (ash 1 34))))))) 
      (unless (eq (first d) :ok) (fnn-fault "chain link ~d refused: ~(~a~)" g (second d)))
      d)))

(defun fnn-spk-chain-links (store)
  "The selected chain, oldest first: ((G . DECODED) ...), checked link to link."
  (let ((sel (fnn-spk-chain-selection store)) (links nil))
    (when sel
      (let ((g (first sel)) (want (second sel)) (count 0))
        (loop
          (let ((d (fnn-spk-read-link store g)))
            (unless (equal (sixth d) want) (fnn-fault "chain link ~d header digest mismatch" g))
            (push (cons g d) links)
            (incf count)
            (when (> count 1000000) (fnn-fault "chain longer than bound"))
            (when (= (second d) 0)
              (unless (= (fourth d) (fnn-core 'fn-spk-no-pred))
                (fnn-fault "first chain link names a predecessor"))
              (return))
            (let ((pred (fnn-spk-read-link store (fourth d))))
              (unless (= (third pred) (second d)) (fnn-fault "chain links are not contiguous at ~d" g))
              (setq g (fourth d) want (fifth d)))))))
    links))

(defun fnn-spk-chain-boundary (store)
  (let ((sel (fnn-spk-chain-selection store)))
    (if sel
        (let ((d (fnn-spk-read-link store (first sel))))
          (unless (equal (sixth d) (second sel)) (fnn-fault "selected chain link digest mismatch"))
          (third d))
        0)))

(defun fnn-spk-chain-records (store)
  (loop for (nil . d) in (fnn-spk-chain-links store) append (eighth d)))

;;; The open callbacks: a selected chain replaces the single-pack authority.
(defvar *fnn-spk-old-lower* *fnn-pack-lower-bound-callback*)
(defvar *fnn-spk-old-recover* *fnn-pack-recover-callback*)

(defun fnn-spk-lower-bound (store)
  (if (fnn-spk-chain-selection store)
      (fnn-spk-chain-boundary store)
      (funcall *fnn-spk-old-lower* store)))

(defun fnn-spk-recover-records (store records sequences actual-lower)
  (if (not (fnn-spk-chain-selection store))
      (funcall *fnn-spk-old-recover* store records sequences actual-lower)
      (let* ((chain (fnn-spk-chain-records store))
             (boundary (length chain))
             (kept nil))
        ;; A covered file that survived an interrupted reclaim must be the
        ;; link's record byte for byte, or its stub.
        (loop for r in records for s in sequences do
          (if (< s boundary)
              (let ((c (nth s chain)))
                (unless (or (equal (fnn-octet-list r) c)
                            (fnn-core 'fn-spk-stub-body-p (fnn-octet-list r))
                            (fnn-core 'fn-spk-stub-body-p c))
                  (fnn-checkpoint-corrupt "surviving covered record ~d differs from its chain link" s)))
              (push r kept)))
        (setq kept (nreverse kept))
        (when (and kept (/= (first (member-if (lambda (s) (>= s boundary)) sequences)) boundary))
          (fnn-checkpoint-corrupt "suffix does not start at the chain boundary"))
        (append (mapcar #'fnn-as-octets chain) kept))))

(setq *fnn-pack-lower-bound-callback* #'fnn-spk-lower-bound)
(setq *fnn-pack-recover-callback* #'fnn-spk-recover-records)

(defun fnn-spk-chain-generations (store)
  (let ((dir (fnn-spk-chain-dir store)))
    (if (fnn-lstat dir)
        (loop for name in (fnn-list-directory dir)
              when (and (= (length name) 30) (string= (subseq name 0 5) "link-"))
                collect (parse-integer name :start 5 :end 25))
        nil)))

(defun fnn-spk-publish-link (store g octets)
  "Stage, fsync, link to the final name (never replacing), fsync the directory."
  (let ((final (fnn-spk-link-path store g))
        (stage (fnn-join (fnn-staging store) (format nil ".stage-link-~d-~a" (sb-posix:getpid) (fnn-random-hex 12)))))
    (when (fnn-lstat final) (fnn-fault "chain link ~d already exists" g))
    (fnn-write-staged stage (fnn-seal octets))
    (fnn-spk-cut "link-staged")
    (fnn-link stage final)
    (fnn-spk-cut "link-linked")
    (fnn-fsync-dir (fnn-spk-chain-dir store))
    (ignore-errors (fnn-unlink stage))))

(defun fnn-spk-select-link (store g header-digest)
  (let ((payload (fnn-octets (append (fnn-core 'fn-spk-u64 g) header-digest))))
    (fnn-spk-replace-file store (fnn-spk-chain-dir store) (fnn-spk-chain-selection-path store)
                          (fnn-seal payload) "chain-selection")))

(defun fnn-spk-compact-chain (root args)
  (let* ((per (let ((p (member "--link-events" args :test #'string=)))
                (if p (parse-integer (second p)) 4096)))
         (max-octets (fnn-core 'fn-store-checkpoint-compaction-max-octets))
         (t0 (get-internal-real-time)))
    (multiple-value-bind (store records) (fnn-open-live-store root t)
      (unwind-protect
           (let* ((t-open (get-internal-real-time))
                  (sel (fnn-spk-chain-selection store))
                  (boundary (fnn-spk-chain-boundary store))
                  (uncovered (nthcdr boundary records))
                  (pred (if sel (first sel) (fnn-core 'fn-spk-no-pred)))
                  (pred-digest (if sel (second sel) (make-list 32 :initial-element 0)))
                  (g (1+ (reduce #'max (fnn-spk-chain-generations store) :initial-value -1)))
                  (made 0) (lower boundary))
             (when (fnn-lstat (fnn-pack-selection-path store))
               (fnn-refuse "a single-pack selection exists; the spike chain does not adopt it"))
             (when (null uncovered)
               (fnn-out "chain nothing to compact boundary=~d" boundary)
               (return-from fnn-spk-compact-chain +fnn-exit-ok+))
             (fnn-safe-directory (fnn-spk-chain-dir store) t)
             (setf (fnn-store-fenced store) t)
             ;; Links of at most PER events and MAX-OCTETS body octets.
             (loop while uncovered do
               (let ((batch nil) (octets 0))
                 (loop while (and uncovered (< (length batch) per)
                                  (or (null batch) (<= (+ octets (length (first uncovered))) max-octets)))
                       do (incf octets (length (first uncovered)))
                          (push (fnn-octet-list (pop uncovered)) batch))
                 (setq batch (nreverse batch))
                 (let* ((payload (fnn-core 'fn-spk-link-encode lower pred pred-digest batch nil))
                        (d (fnn-core 'fn-spk-link-decode payload)))
                   (unless (eq (first d) :ok) (fnn-fault "ACL2 refused its own link: ~a" (second d)))
                   (fnn-spk-publish-link store g (fnn-octets payload))
                   (setq pred g pred-digest (sixth d) lower (third d))
                   (incf g) (incf made))))
             (fnn-spk-select-link store pred pred-digest)
             (fnn-spk-cut "chain-selected")
             ;; Reclaim the covered transaction files.
             (let ((n 0))
               (dolist (name (fnn-list-directory (fnn-transactions store)))
                 (let ((s (ignore-errors (parse-integer name :junk-allowed t))))
                   (when (and s (< s lower)
                              (string= name (fnn-transaction-name s)))
                     (fnn-unlink (fnn-join (fnn-transactions store) name))
                     (incf n)
                     (when (= n 1) (fnn-spk-cut "chain-reclaim-unlink")))))
               (fnn-fsync-dir (fnn-transactions store))
               (setf (fnn-store-fenced store) nil)
               (fnn-out "chain compacted links=~d boundary=~d files-reclaimed=~d open-ms=~d total-ms=~d ~a"
                        made lower n
                        (round (* 1000 (- t-open t0)) internal-time-units-per-second)
                        (round (* 1000 (- (get-internal-real-time) t0)) internal-time-units-per-second)
                        (fnn-open-report store)))
             +fnn-exit-ok+)
        (fnn-store-close store)))))

(defun fnn-spk-chain-rebody (store pairs)
  "Rewrite each chain link that holds a stubbed record, in place, same header."
  (let ((links (fnn-spk-chain-links store)) (n 0))
    (dolist (entry links)
      (destructuring-bind (g . d) entry
        (let* ((lo (second d)) (hi (third d))
               (mine (remove-if-not (lambda (p) (and (>= (car p) lo) (< (car p) hi))) pairs)))
          (when mine
            (let ((bodies (copy-list (eighth d))))
              (dolist (p mine) (setf (nth (- (car p) lo) bodies) (fnn-octet-list (cdr p))))
              (let* ((path (fnn-spk-link-path store g))
                     (x (fnn-octet-list (fnn-spk-unseal (fnn-read-regular-bounded path (ash 1 34)))))
                     (new (fnn-core 'fn-spk-link-rebody x bodies)))
                (unless (fnn-octet-list-p new) (fnn-fault "ACL2 refused the link rewrite ~d" g))
                (fnn-spk-replace-file store (fnn-spk-chain-dir store) path
                                      (fnn-seal (fnn-octets new)) "reclaim-link")
                (incf n)))))))
    n))

(defun fnn-spk-chain-retire (root)
  (multiple-value-bind (store records) (fnn-open-live-store root t)
    (declare (ignore records))
    (unwind-protect
         (let* ((keep (mapcar #'car (fnn-spk-chain-links store)))
                (all (fnn-spk-chain-generations store))
                (gone (set-difference all keep)))
           (dolist (g gone) (fnn-unlink (fnn-spk-link-path store g)))
           (when gone (fnn-fsync-dir (fnn-spk-chain-dir store)))
           (fnn-out "chain retired=~d kept=~d" (length gone) (length keep))
           +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-spk-history-digest (root)
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (unwind-protect
         (let ((d (fnn-core 'fn-spk-digests (mapcar #'fnn-octet-list records))))
           (fnn-out "history records=~d digest=~a chain-boundary=~d links=~d ~a"
                    (length records) (fnn-hex (fnn-octets (fnn-core 'fn-frame-digest d)))
                    (fnn-spk-chain-boundary store) (length (fnn-spk-chain-links store))
                    (fnn-open-report store))
           +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-spk-store-verb (root rest)
  (let ((command (first rest)) (args (rest rest)))
    (cond ((null command) (error 'fnn-usage-error :message "spike-store ROOT COMMAND"))
          ((string= command "release") (fnn-spk-release root args))
          ((string= command "reclaim") (fnn-spk-reclaim root args))
          ((string= command "compact-chain") (fnn-spk-compact-chain root args))
          ((string= command "chain-retire") (fnn-spk-chain-retire root))
          ((string= command "history-digest") (fnn-spk-history-digest root))
          (t (error 'fnn-usage-error :message (format nil "unknown spike-store command ~a" command))))))

(fnn-register-verb "spike-store" #'fnn-spk-store-verb)
