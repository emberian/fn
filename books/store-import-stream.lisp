; fn: `store import' a chunk at a time (lane obligations-paged-archive,
; 2026-09-28; PRF-369).  Prefix `fn-sxi-'.
;
; The import read every record of the archive into one list and called
; fn-sxp-import-plan over it (books/store-export.lisp): at 1,000,000 records
; of 2 KiB that list and the MANIFEST as one octet list lived at once.  The
; host (host/native/io.lisp fnn-command-store-import) now reads the archive a
; chunk of records at a time (the export's quantum, +fnn-export-chunk+) and
; asks ACL2 per step:
;   fn-sxi-head   the head entries (profile, frontier, configuration records)
;                 and the MANIFEST octets they must be;
;   fn-sxi-want   one chunk's record entries' MANIFEST octets;
;   fn-sxi-step   the chunk checked against the MANIFEST octets the host read
;                 at its place (as many as fn-sxi-want's) and its sequence
;                 checked, carrying the state to the next chunk; the records
;                 it returns are the ones the store receives;
;   fn-sxi-final  the verdict, after the host read what follows the last
;                 chunk's lines (at most one octet: the MANIFEST must end).
; The MANIFEST is read at its place a piece at a time, never whole.  The work
; and allocation per step are one chunk's (a quantum, never a bound on the
; archive: every record is in exactly one chunk).
;
; KEYSTONE fn-sxi-stream-plan-is-the-import-plan: for EVERY chunking of the
; records and EVERY MANIFEST, the host's loop over these steps
; (fn-sxi-stream-plan, the composition in the host's order) decides exactly
; what fn-sxp-import-plan decides over the whole archive -- the same refusal
; by the same name, or the same profile, configuration records and records
; (the chunks' records joined in order).  No hypotheses.  So PRF-205's round
; trip (fn-sxp-import-of-export-replays-the-same-history) holds of the
; streamed import.

(in-package "ACL2")
(include-book "store-export-stream")

; -----------------------------------------------------------------------------
; The steps the host calls.

; A read of at most N octets from the front of XS (a short read at the end of
; the file): what the host's bounded read returns.
(defun fn-sxi-first (n xs)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom xs))
      nil
    (cons (car xs) (fn-sxi-first (1- n) (cdr xs)))))

; The state carried between chunks: (MISMATCH OUT-OF-SEQUENCE PREVIOUS) --
; the first MANIFEST mismatch's entry name, the first out-of-sequence
; sequence, the last sequence seen.
(defun fn-sxi-st (mm oos prev)
  (declare (xargs :guard t))
  (list mm oos prev))
(defun fn-sxi-st-mm (st) (declare (xargs :guard t)) (fn-ag-car st))
(defun fn-sxi-st-oos (st) (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr st)))
(defun fn-sxi-st-prev (st)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr st))))

; The head: (ENTRIES . LINES).
(defun fn-sxi-head (profile frontier configs)
  (declare (xargs :guard t))
  (let ((entries (fn-sxp-head-entries profile frontier configs)))
    (cons entries (fn-sxp-manifest entries))))

; The MANIFEST octets ENTRIES must be at their place, checked against PIECE,
; the octets the host read there (as many as LINES, fewer at the file's
; end).  LINES is the want step's value; equal octets are the common case
; and cost one comparison, anything else names the first entry whose line
; PIECE does not carry.
(defun fn-sxi-check (entries lines piece)
  (declare (xargs :guard t))
  (if (equal piece lines)
      nil
    (fn-sxp-manifest-mismatch entries piece)))

; The start state after the head's check.
(defun fn-sxi-start (entries lines piece)
  (declare (xargs :guard t))
  (fn-sxi-st (fn-sxi-check entries lines piece) nil nil))

(defun fn-sxi-want (records)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sxp-manifest (fn-sxp-record-entries records)))

; The last sequence of RECORDS as fn-sxp-out-of-sequence carries it.
(defun fn-sxi-last-seq (records prev)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-sxi-last-seq (cdr records) (if (consp (car records)) (caar records) nil))
    prev))

; One chunk: (ST' . RECORDS'), RECORDS' the chunk's records as the new store
; receives them.  Two parts, each keeping its first failure: the MANIFEST (a
; mismatch ends the walk: the host stops reading) and the sequence.
; fn-sxi-final ranks them as fn-sxp-import-plan does.
(defun fn-sxi-step (st records lines piece)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sxi-st-mm st)
      (cons st nil)
    (let ((mm (fn-sxi-check (fn-sxp-record-entries records) lines piece)))
      (if mm
          (cons (fn-sxi-st mm nil nil) nil)
        (cons (fn-sxi-st nil
                         (or (fn-sxi-st-oos st)
                             (fn-sxp-out-of-sequence records (fn-sxi-st-prev st)))
                         (fn-sxi-last-seq records (fn-sxi-st-prev st)))
              records)))))

; The verdict after the last chunk.  TAIL is what the host read after the
; last chunk's lines (at most one octet): a MANIFEST longer than the
; archive's entries is refused under its own name.  (:import VALUES FRONTIER
; CONFIGS) -- the records are the ones the steps returned -- or the refusal
; fn-sxp-import-plan names.
(defun fn-sxi-final (st tail profile frontier configs request)
  (declare (xargs :guard t :verify-guards nil))
  (let ((saved (fn-bs-config-decode profile)))
    (cond ((fn-sxi-st-mm st) (list :refused :manifest-mismatch (fn-sxi-st-mm st)))
          ((consp tail) (list :refused :manifest-mismatch *fn-sxp-manifest-name*))
          ((fn-sxi-st-oos st)
           (list :refused :record-out-of-sequence (fn-sxi-st-oos st)))
          ((not (fn-sxp-config-names-increasingp configs nil))
           (list :refused :config-out-of-sequence))
          ((null saved) (list :refused :profile :store-format))
          ((not (fn-bs-profile-requestp request))
           (list :refused :profile :request))
          ((null (cadr request))
           (list :import saved frontier configs))
          (t (let ((values (fn-bs-profile-resolve request saved)))
               (if (and (consp values) (equal (car values) :invalid))
                   (list :refused :profile
                         (if (consp (cdr values)) (cadr values) :request))
                 (list :import values frontier configs)))))))

; Pass two (the records written into the staged store) must decide what pass
; one decided: the host refuses the archive by name (archive-changed) when
; they differ.  ACL2 compares them.
(defun fn-sxi-same-verdict (a b)
  (declare (xargs :guard t))
  (equal a b))

; -----------------------------------------------------------------------------
; The host's loop, as a specification (the host never calls these): the
; chunks CHUNKS walked over the MANIFEST octets M the file holds from the
; chunk's place, every read at most as many octets as the step wants.
; (ST RECORDS REST): the last state, the records the steps returned joined
; in order, and the MANIFEST octets after the last chunk's.

(defun fn-sxi-walk (st chunks m)
  (declare (xargs :guard t :verify-guards nil :measure (len chunks)))
  (if (and (consp chunks) (not (fn-sxi-st-mm st)))
      (let* ((lines (fn-sxi-want (car chunks)))
             (r (fn-sxi-step st (car chunks) lines
                             (fn-sxi-first (len lines) m)))
             (w (fn-sxi-walk (car r) (cdr chunks) (nthcdr (len lines) m))))
        (list (car w) (append (cdr r) (cadr w)) (caddr w)))
    (list st nil m)))

(defun fn-sxi-stream-plan (m profile frontier configs chunks request)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((head (fn-sxi-head profile frontier configs))
         (lines (cdr head))
         (st0 (fn-sxi-start (car head) lines (fn-sxi-first (len lines) m)))
         (w (fn-sxi-walk st0 chunks (nthcdr (len lines) m)))
         (v (fn-sxi-final (car w) (fn-sxi-first 1 (caddr w))
                          profile frontier configs request)))
    (if (equal (car v) :import)
        (append v (list (cadr w)))
      v)))

; -----------------------------------------------------------------------------
; The proof.  Two parts, each a property of the walk over any chunking: the
; MANIFEST's first mismatch is the whole archive's (the pieces the host reads
; at each chunk's place carry exactly that chunk's lines); the sequence's
; first failure is the joined records'.

(local
 (defthm fn-sxi-st-accessors
   (and (equal (fn-sxi-st-mm (fn-sxi-st a b c)) a)
        (equal (fn-sxi-st-oos (fn-sxi-st a b c)) b)
        (equal (fn-sxi-st-prev (fn-sxi-st a b c)) c))))

(local (in-theory (disable fn-sxi-st fn-sxi-st-mm fn-sxi-st-oos fn-sxi-st-prev)))

(local
 (defthm fn-sxi-drop-is-nthcdr
   (equal (fn-sxp-drop n xs) (nthcdr n xs))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-sxi-nthcdr-nthcdr
   (implies (and (natp a) (natp b))
            (equal (nthcdr a (nthcdr b m)) (nthcdr (+ a b) m)))
   :hints (("Goal" :in-theory (enable nthcdr)))))

; The MANIFEST check without its last test (octets left over).
(defun fn-sxi-mm (entries m)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (let ((line (fn-sxp-manifest-line (car entries))))
        (if (fn-sxp-prefixp line m)
            (fn-sxi-mm (cdr entries) (nthcdr (len line) m))
          (if (consp (car entries)) (caar entries) nil)))
    nil))

; Every entry has a name (every entry the export and the import build).
(defun fn-sxi-namedp (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (and (consp (car entries)) (caar entries) (fn-sxi-namedp (cdr entries)))
    t))

(local
 (defthm fn-sxi-mismatch-is-mm
   (implies (fn-sxi-namedp entries)
            (equal (fn-sxp-manifest-mismatch entries m)
                   (or (fn-sxi-mm entries m)
                       (if (consp (nthcdr (len (fn-sxp-manifest entries)) m))
                           *fn-sxp-manifest-name*
                         nil))))
   :hints (("Goal" :induct (fn-sxi-mm entries m)
            :in-theory (disable fn-sxp-manifest-line)))))

(local
 (defthm fn-sxi-mm-of-append
   (implies (fn-sxi-namedp a)
            (equal (fn-sxi-mm (append a b) m)
                   (or (fn-sxi-mm a m)
                       (fn-sxi-mm b (nthcdr (len (fn-sxp-manifest a)) m)))))
   :hints (("Goal" :induct (fn-sxi-mm a m)
            :in-theory (disable fn-sxp-manifest-line)))))

(local
 (defthm fn-sxi-prefixp-of-first
   (implies (and (natp k) (<= (len line) k))
            (equal (fn-sxp-prefixp line (fn-sxi-first k m))
                   (fn-sxp-prefixp line m)))))

(local
 (defthm fn-sxi-nthcdr-of-first
   (implies (and (natp k) (natp j) (<= j k))
            (equal (nthcdr j (fn-sxi-first k m))
                   (fn-sxi-first (- k j) (nthcdr j m))))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defun fn-sxi-mm-first-ind (a m k)
   (declare (xargs :guard t :verify-guards nil))
   (if (consp a)
       (let ((line (fn-sxp-manifest-line (car a))))
         (fn-sxi-mm-first-ind (cdr a) (nthcdr (len line) m) (- (nfix k) (len line))))
     (list m k))))

(local
 (defthm fn-sxi-mm-of-first
   (implies (and (natp k) (<= (len (fn-sxp-manifest a)) k))
            (equal (fn-sxi-mm a (fn-sxi-first k m))
                   (fn-sxi-mm a m)))
   :hints (("Goal" :induct (fn-sxi-mm-first-ind a m k)
            :in-theory (disable fn-sxp-manifest-line)))))

(local
 (defthm fn-sxi-len-first
   (<= (len (fn-sxi-first k m)) (nfix k))
   :rule-classes :linear))

(local
 (defthm fn-sxi-nthcdr-past-len
   (implies (<= (len xs) (nfix n))
            (not (consp (nthcdr n xs))))
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-sxi-prefixp-of-append
   (fn-sxp-prefixp xs (append xs ys))))

(local
 (defthm fn-sxi-nthcdr-len-append
   (equal (nthcdr (len xs) (append xs ys)) ys)
   :hints (("Goal" :in-theory (enable nthcdr)))))

(local
 (defthm fn-sxi-mm-of-own-manifest
   (equal (fn-sxi-mm entries (fn-sxp-manifest entries)) nil)
   :hints (("Goal" :in-theory (disable fn-sxp-manifest-line)))))

; The check the host calls is the MANIFEST check at the chunk's place.
(local
 (defthm fn-sxi-check-is-mismatch-of-piece
   (implies (fn-sxi-namedp entries)
            (equal (fn-sxi-check entries (fn-sxp-manifest entries)
                                 (fn-sxi-first (len (fn-sxp-manifest entries)) m))
                   (fn-sxi-mm entries m)))
   :hints (("Goal" :use ((:instance fn-sxi-mm-of-first (a entries)
                                    (k (len (fn-sxp-manifest entries)))))
            :in-theory (disable fn-sxi-mm-of-first fn-sxp-manifest-line
                                fn-sxp-manifest fn-sxp-manifest-mismatch)))))

(local
 (defthm fn-sxi-namedp-of-append
   (equal (fn-sxi-namedp (append a b))
          (and (fn-sxi-namedp a) (fn-sxi-namedp b)))))
(local
 (defthm fn-sxi-namedp-of-record-entries
   (fn-sxi-namedp (fn-sxp-record-entries records))))
(local
 (defthm fn-sxi-namedp-of-config-entries
   (fn-sxi-namedp (fn-sxp-config-entries configs))))
(local
 (defthm fn-sxi-namedp-of-head-entries
   (fn-sxi-namedp (fn-sxp-head-entries profile frontier configs))))
(local
 (defthm fn-sxi-manifest-of-atom
   (implies (atom entries) (equal (fn-sxp-manifest entries) nil))))

(local
 (defthm fn-sxi-walk-mm
   (implies (not (fn-sxi-st-mm st))
            (equal (fn-sxi-st-mm (car (fn-sxi-walk st chunks m)))
                   (fn-sxi-mm (fn-sxp-record-entries (fn-sxp-chunks-records chunks)) m)))
   :hints (("Goal" :induct (fn-sxi-walk st chunks m)
            :in-theory (disable fn-sxp-manifest-line fn-sxp-manifest
                                fn-sxp-record-entries fn-sxi-check
                                fn-sxp-out-of-sequence fn-sxi-last-seq)))))

(local
 (defthm fn-sxi-walk-rest
   (implies (and (not (fn-sxi-st-mm st))
                 (not (fn-sxi-mm (fn-sxp-record-entries (fn-sxp-chunks-records chunks)) m)))
            (equal (caddr (fn-sxi-walk st chunks m))
                   (nthcdr (len (fn-sxp-manifest
                                 (fn-sxp-record-entries (fn-sxp-chunks-records chunks))))
                           m)))
   :hints (("Goal" :induct (fn-sxi-walk st chunks m)
            :in-theory (disable fn-sxp-manifest-line fn-sxp-manifest
                                fn-sxp-record-entries fn-sxi-check
                                fn-sxp-out-of-sequence fn-sxi-last-seq)))))

(local
 (defthm fn-sxi-oos-of-append
   (equal (fn-sxp-out-of-sequence (append a b) prev)
          (or (fn-sxp-out-of-sequence a prev)
              (fn-sxp-out-of-sequence b (fn-sxi-last-seq a prev))))))

(local
 (defthm fn-sxi-last-seq-of-append
   (equal (fn-sxi-last-seq (append a b) prev)
          (fn-sxi-last-seq b (fn-sxi-last-seq a prev)))))

(local
 (defthm fn-sxi-last-seq-of-atom
   (implies (atom x) (equal (fn-sxi-last-seq x p) p))))

(local
 (defthm fn-sxi-oos-of-atom
   (implies (atom x) (equal (fn-sxp-out-of-sequence x p) nil))))

(local
 (defthm fn-sxi-walk-records
   (implies (and (not (fn-sxi-st-mm st))
                 (not (fn-sxi-mm (fn-sxp-record-entries (fn-sxp-chunks-records chunks)) m)))
            (equal (cadr (fn-sxi-walk st chunks m))
                   (fn-sxp-chunks-records chunks)))
   :hints (("Goal" :induct (fn-sxi-walk st chunks m)
            :in-theory (disable fn-sxp-manifest-line fn-sxp-manifest
                                fn-sxp-record-entries fn-sxi-check
                                fn-sxp-out-of-sequence fn-sxi-last-seq)))))

(local
 (defthm fn-sxi-walk-oos
   (implies (and (not (fn-sxi-st-mm st))
                 (not (fn-sxi-mm (fn-sxp-record-entries (fn-sxp-chunks-records chunks)) m)))
            (and (equal (fn-sxi-st-oos (car (fn-sxi-walk st chunks m)))
                        (or (fn-sxi-st-oos st)
                            (fn-sxp-out-of-sequence (fn-sxp-chunks-records chunks)
                                                    (fn-sxi-st-prev st))))
                 (equal (fn-sxi-st-prev (car (fn-sxi-walk st chunks m)))
                        (fn-sxi-last-seq (fn-sxp-chunks-records chunks)
                                         (fn-sxi-st-prev st)))))
   :hints (("Goal" :induct (fn-sxi-walk st chunks m)
            :in-theory (disable fn-sxp-manifest-line fn-sxp-manifest
                                fn-sxp-record-entries fn-sxi-check
                                fn-sxp-out-of-sequence fn-sxi-last-seq)))))

(local
 (defthm fn-sxi-consp-first-1
   (equal (consp (fn-sxi-first 1 x)) (consp x))
   :hints (("Goal" :expand ((fn-sxi-first 1 x))))))

(local
 (defthm fn-sxi-walk-at-mm
   (implies (fn-sxi-st-mm st)
            (equal (fn-sxi-walk st chunks m) (list st nil m)))))

; KEYSTONE (the subject: the steps host/native/io.lisp
; fnn-command-store-import calls -- fn-sxi-head, fn-sxi-start, per chunk
; fn-sxi-want and fn-sxi-step, then fn-sxi-final -- composed in the host's
; order, the MANIFEST read at each step's place).  No hypotheses.
(defthm fn-sxi-stream-plan-is-the-import-plan
  (equal (fn-sxi-stream-plan m profile frontier configs chunks request)
         (fn-sxp-import-plan m profile frontier configs
                             (fn-sxp-chunks-records chunks) request))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sxi-stream-plan fn-sxi-final fn-sxi-head fn-sxi-start
                            fn-sxp-import-plan)
                           (fn-sxp-entries fn-sxp-head-entries
                            fn-sxp-manifest-line fn-sxp-manifest
                            fn-sxp-record-entries fn-sxp-config-entries
                            fn-sxi-check fn-sxi-walk fn-sxi-mm
                            fn-sxp-out-of-sequence fn-sxi-last-seq
                            fn-bs-config-decode fn-bs-profile-requestp
                            fn-bs-profile-resolve
                            fn-sxp-config-names-increasingp)))))

; The executable steps run guard-verified.
(verify-guards fn-sxi-want)
(verify-guards fn-sxi-step
  :hints (("Goal" :in-theory (disable fn-sxi-check fn-sxp-record-entries
                                      fn-sxp-out-of-sequence fn-sxi-last-seq
                                      fn-sxi-mismatch-is-mm))))
(verify-guards fn-sxi-final)
