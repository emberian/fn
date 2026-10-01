; fn: the committed history image read back from the page file (lane
; arena-store-7, 2026-09-28, milestone (b1)).  Prefix fn-hrs- (the
; concrete: fn-hrc-).
;
; The store's records (books/store-files.lisp `fn-sf-records') become the
; committed image's history followed by the suffix appended since.  A
; value cannot carry a ghost, so the image's history is a FUNCTION of a
; small handle: `fn-hrs-disk-history' HANDLE decodes the image the page
; file holds, read through the host's page fill `fn-pgs-fill-realize'
; (A-PGS-HOST-IO; no new assumption).  It is the lazy full decode an
; unmigrated reader pays; readers move to `fn-hrecs-read' one at a time.
;
; HANDLE = (:hrs-handle FILE REC SALT N LENS STARTS NP): the page file,
; the page store's committed root record REC (books/pagestore.lisp
; pgs-rec-*: txid, directory address, page count, directory digest), the
; image's MKEY salt and its header (N LENS STARTS NP, `fn-hp-x-header').
;
; The decode, over a fresh fn-hrecs$c: the directory run and every table
; page from the file, each checked by the page store's open
; (`pgs-x-open-dir', `pgs-x-open-table-page' :eager); the header adopted;
; then rows 0..N-1 by the retry loop (`fn-hrc-get', the concrete twin of
; `fn-hrecs-get': a (:need-page P PHYS) is served by one fill of P from
; the file and its digest check).  It answers exactly N elements; a row
; that does not read (:ok) makes the decode unclean, and
; `fn-hrs-disk-history' then signals the fault by name (a recovery
; event), never a silent value.
;
; KEYSTONE fn-hrs-disk-history-is-image: when the page file holds H's
; image at the addresses the committed tables name (`fn-hrs-disk-holds')
; and the decode is clean, the decode is H.
(in-package "ACL2")
(include-book "history-records")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; A. The handle.

(defun fn-hrs-handlep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 8) (eq (nth 0 x) :hrs-handle)
       (natp (nth 3 x)) (natp (nth 4 x))
       (nat-listp (nth 5 x)) (equal (len (nth 5 x)) 5)
       (nat-listp (nth 6 x)) (equal (len (nth 6 x)) 5)
       (natp (nth 7 x))))

(defun fn-hrs-handle (file rec salt n lens starts np)
  (declare (xargs :guard t))
  (list :hrs-handle file rec salt n lens starts np))

(defun fn-hrs-h-file (x) (declare (xargs :guard t)) (nth 1 (true-list-fix x)))
(defun fn-hrs-h-rec (x) (declare (xargs :guard t)) (nth 2 (true-list-fix x)))
(defun fn-hrs-h-salt (x) (declare (xargs :guard t)) (nfix (nth 3 (true-list-fix x))))
(defun fn-hrs-h-n (x) (declare (xargs :guard t)) (nfix (nth 4 (true-list-fix x))))
(defun fn-hrs-h-lens (x) (declare (xargs :guard (fn-hrs-handlep x))) (nth 5 x))
(defun fn-hrs-h-starts (x) (declare (xargs :guard (fn-hrs-handlep x))) (nth 6 x))
(defun fn-hrs-h-np (x) (declare (xargs :guard t)) (nfix (nth 7 (true-list-fix x))))

; -----------------------------------------------------------------------------
; B. The page store's open from the file: the directory run and every
; table page, each filled through `fn-pgs-fill-realize' and checked.

; The page store's list put for SEL 1 and 2 is the frame's put
; (books/assumptions-pgs-host-io.lisp), and its length the frame's: what
; the in-place fill below is bridged by.
; (used by name in the guard proof below, never as rewrite rules: the proofs
; over fn-hrs-fill-run reason about pgs-x-fill as it is)
(defthm pgs-x-u64-listp-is-fn-pgs-u64-listp
  (equal (pgs-x-u64-listp ws) (fn-pgs-u64-listp ws))
  :rule-classes nil)

(defthm pgs-x-len-is-frame-len
  (implies (pgs-x-sel-p sel)
           (equal (pgs-x-len sel pgs-mem) (fn-pgs-frame-len sel pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-len fn-pgs-frame-len)))
  :rule-classes nil)

(defthm pgs-x-fill-is-frame-put
  (implies (pgs-x-sel-p sel)
           (equal (pgs-x-fill sel a ws pgs-mem) (fn-pgs-frame-put sel a ws pgs-mem)))
  :hints (("Goal" :induct (pgs-x-fill sel a ws pgs-mem)
           :in-theory (enable pgs-x-fill pgs-x-put fn-pgs-frame-put)))
  :rule-classes nil)

(defun fn-hrs-fill-run (file addr k sel a pgs-mem)
  ; K pages from page ADDR of FILE into SEL's words from A.  A page whose
  ; words are not 2048 u64 words, or do not fit, is left as it was: the
  ; page store's digest check then refuses it.  In the logic the list form;
  ; what runs is the in-place fill (lane page-word-boundary: the host puts
  ; the page's words into SEL's array itself, `fn-pgs-fill-frame'), the same
  ; state by A-PGS-HOST-IO's frame constraint; the words-shape refusal is
  ; unreachable there (the page's words are 2048 u64 words).
  (declare (xargs :stobjs pgs-mem :guard (and (pgs-x-sel-p sel) (natp addr) (natp k) (natp a))
                  :measure (nfix k)
                  :guard-hints (("Goal" :in-theory (disable pgs-x-fill fn-pgs-frame-put fn-pgs-frame-len pgs-x-len)
                                 :use ((:instance fn-pgs-page-words-shape)
                                       (:instance fn-pgs-page-words-u64)
                                       (:instance pgs-x-u64-listp-is-fn-pgs-u64-listp (ws (fn-pgs-page-words file addr)))
                                       (:instance pgs-x-len-is-frame-len)
                                       (:instance pgs-x-fill-is-frame-put (ws (fn-pgs-page-words file addr))))))))
  (if (zp k)
      pgs-mem
    (let* ((pgs-mem (mbe :logic (let ((ws (fn-pgs-fill-realize file addr)))
                                  (if (and (pgs-x-u64-listp ws) (<= (+ a (len ws)) (pgs-x-len sel pgs-mem)))
                                      (pgs-x-fill sel a ws pgs-mem)
                                    pgs-mem))
                         :exec (if (<= (+ a 2048) (pgs-x-len sel pgs-mem))
                                   (fn-pgs-fill-frame file addr sel a pgs-mem)
                                 pgs-mem))))
      (fn-hrs-fill-run file (+ 1 addr) (- k 1) sel (+ a 2048) pgs-mem))))

(defun fn-hrs-load-dir (file rec pgs-mem fn-octets-pg)
  ; pgs-m from *pgs-x-dir-base* := REC's directory run, then the open's
  ; verdict on it: (mv VERDICT pgs-mem fn-octets-pg), nil when sound.
  (declare (xargs :stobjs (pgs-mem fn-octets-pg) :guard t))
  (let* ((nt (pgs-x-ntables (pgs-rec-npages rec)))
         (m (pgs-ptab-run-pages nt))
         (pgs-mem (resize-pgs-m *pgs-x-dir-base* pgs-mem))
         (pgs-mem (resize-pgs-m (+ *pgs-x-dir-base* (* 2048 m)) pgs-mem))
         (pgs-mem (fn-hrs-fill-run file (pgs-rec-dir-addr rec) m 1 *pgs-x-dir-base* pgs-mem)))
    (mv-let (v fn-octets-pg)
      (pgs-x-open-dir rec pgs-mem fn-octets-pg)
      (mv v pgs-mem fn-octets-pg))))

(defun fn-hrs-load-tables (tabs file rec pgs-mem fn-octets-pg)
  ; Each (T PHYS) of TABS: table page T from page PHYS, then its check.
  (declare (xargs :stobjs (pgs-mem fn-octets-pg) :guard (true-listp tabs)))
  (if (atom tabs)
      (mv nil pgs-mem fn-octets-pg)
    (let* ((tp (nfix (first (true-list-fix (car tabs)))))
           (phys (nfix (second (true-list-fix (car tabs)))))
           (pgs-mem (fn-hrs-fill-run file phys 1 2 (* 2048 tp) pgs-mem)))
      (mv-let (v pgs-mem fn-octets-pg)
        (pgs-x-open-table-page tp rec :eager pgs-mem fn-octets-pg)
        (if v
            (mv v pgs-mem fn-octets-pg)
          (fn-hrs-load-tables (cdr tabs) file rec pgs-mem fn-octets-pg))))))

(defun fn-hrs-size-image (np pgs-mem)
  ; NP image pages: zero words, not resident, clean.
  (declare (xargs :stobjs pgs-mem :guard (natp np)))
  (let* ((pgs-mem (resize-pgs-w 0 pgs-mem)) (pgs-mem (resize-pgs-d 0 pgs-mem))
         (pgs-mem (resize-pgs-v 0 pgs-mem)) (pgs-mem (resize-pgs-w (* 2048 np) pgs-mem))
         (pgs-mem (resize-pgs-d np pgs-mem)))
    (resize-pgs-v np pgs-mem)))

;; The open keeps the stobjs' shapes.
(defthm fn-hrs-fill-run-memp
  (implies (and (pgs-memp pgs-mem) (pgs-x-sel-p sel) (natp a))
           (pgs-memp (fn-hrs-fill-run file addr k sel a pgs-mem))))
(defthm fn-hrs-open-dir-octets
  (implies (fn-octets-pg-p fn-octets-pg)
           (fn-octets-pg-p (mv-nth 1 (pgs-x-open-dir rec pgs-mem fn-octets-pg))))
  :hints (("Goal" :in-theory (union-theories '(pgs-x-open-dir pgs-oct-p-of-words-digest) (theory 'minimal-theory)))))
(defthm fn-hrs-memp-resize-m
  (implies (pgs-memp pgs-mem) (pgs-memp (resize-pgs-m n pgs-mem)))
  :hints (("Goal" :use ((:instance pgs-memp-of-x-resize (s 1))) :in-theory (e/d (pgs-x-resize) (pgs-memp-of-x-resize)))))
(defthm fn-hrs-load-dir-types
  (implies (and (pgs-memp pgs-mem) (fn-octets-pg-p fn-octets-pg))
           (and (pgs-memp (mv-nth 1 (fn-hrs-load-dir file rec pgs-mem fn-octets-pg)))
                (fn-octets-pg-p (mv-nth 2 (fn-hrs-load-dir file rec pgs-mem fn-octets-pg)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hrs-load-dir fn-hrs-open-dir-octets fn-hrs-memp-resize-m fn-hrs-fill-run-memp
                                               pgs-x-sel-p natp (:e natp) (:e pgs-x-sel-p))
                                             (theory 'minimal-theory)))))
(defthm fn-hrs-open-table-page-types
  (implies (and (pgs-memp pgs-mem) (fn-octets-pg-p fn-octets-pg) (natp tp))
           (and (pgs-memp (mv-nth 1 (pgs-x-open-table-page tp rec mode pgs-mem fn-octets-pg)))
                (fn-octets-pg-p (mv-nth 2 (pgs-x-open-table-page tp rec mode pgs-mem fn-octets-pg)))))
  :hints (("Goal" :in-theory (disable pgs-x-ntables pgs-ntables-as-tq pgs-x-table-verdict pgs-x-words-digest ceiling floor))))
(defthm fn-hrs-load-tables-types
  (implies (and (pgs-memp pgs-mem) (fn-octets-pg-p fn-octets-pg))
           (and (pgs-memp (mv-nth 1 (fn-hrs-load-tables tabs file rec pgs-mem fn-octets-pg)))
                (fn-octets-pg-p (mv-nth 2 (fn-hrs-load-tables tabs file rec pgs-mem fn-octets-pg)))))
  :hints (("Goal" :induct (fn-hrs-load-tables tabs file rec pgs-mem fn-octets-pg)
           :in-theory (disable pgs-x-open-table-page fn-hrs-fill-run))))
(defthm fn-hrs-size-image-memp
  (implies (and (pgs-memp pgs-mem) (natp np)) (pgs-memp (fn-hrs-size-image np pgs-mem)))
  :hints (("Goal" :in-theory (disable resize-pgs-w resize-pgs-d resize-pgs-v))))
(defthm fn-hrs-reset-table-memp
  (implies (and (pgs-memp pgs-mem) (natp n)) (pgs-memp (pgs-x-reset-table n pgs-mem)))
  :hints (("Goal" :in-theory (disable resize-pgs-tv pgs-x-resize pgs-x-ntables))))

(defthm fn-hrs-true-listp-open-tables
  (implies (true-listp acc) (true-listp (pgs-x-open-tables j nt txid mode acc pgs-mem))))

(defun fn-hrs-open-pgs (file rec pgs-mem fn-octets-pg)
  ; The committed root REC of FILE, opened: the directory, every table
  ; page (:eager), the image sized, no data page read.
  (declare (xargs :stobjs (pgs-mem fn-octets-pg) :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-hrs-load-dir pgs-x-reset-table fn-hrs-size-image
                                                            pgs-x-open-tables pgs-x-ntables)))))
  (mv-let (v pgs-mem fn-octets-pg)
    (fn-hrs-load-dir file rec pgs-mem fn-octets-pg)
    (if v
        (mv v pgs-mem fn-octets-pg)
      (let* ((npages (pgs-rec-npages rec))
             (pgs-mem (pgs-x-reset-table npages pgs-mem))
             (pgs-mem (fn-hrs-size-image npages pgs-mem))
             (tabs (pgs-x-open-tables 0 (pgs-x-ntables npages) (pgs-rec-txid rec) :eager nil pgs-mem)))
        (fn-hrs-load-tables tabs file rec pgs-mem fn-octets-pg)))))

(defthm fn-hrs-open-pgs-types
  (implies (and (pgs-memp pgs-mem) (fn-octets-pg-p fn-octets-pg))
           (and (pgs-memp (mv-nth 1 (fn-hrs-open-pgs file rec pgs-mem fn-octets-pg)))
                (fn-octets-pg-p (mv-nth 2 (fn-hrs-open-pgs file rec pgs-mem fn-octets-pg)))))
  :hints (("Goal" :in-theory (disable fn-hrs-load-dir fn-hrs-load-tables fn-hrs-size-image pgs-x-reset-table pgs-x-open-tables pgs-x-ntables))))

; -----------------------------------------------------------------------------
; C. The concrete: open the handle's image, the retry loop, the rows.

(defthm fn-hrs-wfp-of-pgs-oct
  (implies (fn-hrc-wfp fn-hrecs$c)
           (fn-hrc-wfp (update-fn-hrc-oct o (update-fn-hrc-pgs p fn-hrecs$c)))))

(defun fn-hrc-open-file (handle fn-hrecs$c)
  ; (mv VERDICT fn-hrecs$c): the page store opened from the handle's root
  ; (nil) and the image's header adopted, or the page store's refusal.
  (declare (xargs :stobjs fn-hrecs$c :guard (and (fn-hrs-handlep handle) (fn-hrc-wfp fn-hrecs$c))
                  :guard-hints (("Goal" :in-theory (disable fn-hrs-open-pgs fn-hrc-wfp fn-hrecs$cp)))))
  (let ((file (fn-hrs-h-file handle)) (rec (fn-hrs-h-rec handle)))
    (mv-let (v fn-hrecs$c)
      (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c))
                  (fn-octets-pg (fn-hrc-oct fn-hrecs$c)))
                 (v pgs-mem fn-octets-pg)
                 (fn-hrs-open-pgs file rec pgs-mem fn-octets-pg)
                 (mv v fn-hrecs$c))
      (if v
          (mv v fn-hrecs$c)
        (let ((fn-hrecs$c (fn-hrc-adopt (fn-hrs-h-salt handle) (fn-hrs-h-n handle) (fn-hrs-h-lens handle)
                                        (fn-hrs-h-starts handle) (fn-hrs-h-np handle) (pgs-rec-txid rec)
                                        fn-hrecs$c)))
          (mv nil fn-hrecs$c))))))

(defun fn-hrc-get (seq file fuel fn-hrecs$c)
  ; `fn-hrecs-get' over the concrete (fn-hrc-get-is-hrecs-get).
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp seq) (natp fuel) (fn-hrc-wfp fn-hrecs$c))
                  :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-hrc-at fn-hrc-fill fn-hrc-phys fn-hrecs$cp fn-hrc-wfp
                                                      fn-hrc-fill-shape fn-hrs-fill-pgs)))
                  :guard-hints (("Goal" :in-theory (disable fn-hrc-at fn-hrc-fill fn-hrc-phys fn-hrecs$cp
                                                            fn-hrc-fill-shape fn-hrs-fill-pgs)))))
  (mv-let (v r) (fn-hrc-at seq fn-hrecs$c)
    (cond ((eq v :ok) (mv :ok r fn-hrecs$c))
          ((not (and (consp v) (eq (car v) :need-page) (consp (cdr v)) (natp (cadr v)))) (mv v nil fn-hrecs$c))
          ((zp fuel) (mv (list :refused :fuel) nil fn-hrecs$c))
          (t (mv-let (fv fn-hrecs$c)
               ; the list form in the logic; the frame fill runs (the same
               ; term by fn-hrc-frame-fill's definition)
               (mbe :logic (fn-hrc-fill (cadr v) (fn-pgs-fill-realize file (fn-hrc-phys (cadr v) fn-hrecs$c)) fn-hrecs$c)
                    :exec (fn-hrc-frame-fill file (fn-hrc-phys (cadr v) fn-hrecs$c) (cadr v) fn-hrecs$c))
               (if (eq fv :ok)
                   (fn-hrc-get seq file (1- fuel) fn-hrecs$c)
                 (mv fv nil fn-hrecs$c)))))))

(defthm fn-hrc-get-wfp
  (implies (fn-hrc-wfp fn-hrecs$c)
           (fn-hrc-wfp (mv-nth 2 (fn-hrc-get seq file fuel fn-hrecs$c))))
  :hints (("Goal" :induct (fn-hrc-get seq file fuel fn-hrecs$c)
           :in-theory (disable fn-hrc-at fn-hrc-fill fn-hrc-phys fn-hrecs$cp fn-hrc-wfp fn-hrc-fill-shape fn-hrs-fill-pgs))))

(defun fn-hrc-rows (i n file ok acc fn-hrecs$c)
  ; Rows I..N-1 onto ACC (newest first): (mv OK ROWS fn-hrecs$c), ROWS
  ; oldest first.  OK: every row answered (:ok (:ok EV)); a row that did
  ; not is nil in ROWS and OK is nil.
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp i) (natp n) (true-listp acc) (fn-hrc-wfp fn-hrecs$c))
                  :measure (nfix (- (nfix n) (nfix i)))
                  :hints (("Goal" :in-theory (disable fn-hrc-get fn-hrc-vlen fn-hrecs$cp fn-hrc-wfp)))
                  :guard-hints (("Goal" :in-theory (disable fn-hrc-get fn-hrc-vlen fn-hrecs$cp)))))
  (if (mbe :logic (zp (- (nfix n) (nfix i))) :exec (<= n i))
      (mv ok (revappend acc nil) fn-hrecs$c)
    (mv-let (v r fn-hrecs$c)
      (fn-hrc-get i file (fn-hrc-vlen fn-hrecs$c) fn-hrecs$c)
      (let ((good (and (eq v :ok) (consp r) (eq (car r) :ok) (consp (cdr r)))))
        (fn-hrc-rows (+ 1 (nfix i)) n file (and ok good) (cons (if good (cadr r) nil) acc) fn-hrecs$c)))))

(defthm fn-hrc-open-file-wfp
  (implies (and (fn-hrc-wfp fn-hrecs$c) (fn-hrs-handlep handle))
           (fn-hrc-wfp (mv-nth 1 (fn-hrc-open-file handle fn-hrecs$c))))
  :hints (("Goal" :in-theory (disable fn-hrs-open-pgs fn-hrecs$cp))))

(defun fn-hrs-disk-decode (handle)
  ; (mv CLEAN ROWS): the image the handle names, decoded from the page file
  ; over a fresh concrete; exactly N rows (N nils when the page store's
  ; open refuses).  CLEAN: the open landed and every row read.
  (declare (xargs :guard (fn-hrs-handlep handle)
                  :guard-hints (("Goal" :in-theory (disable fn-hrc-open-file fn-hrc-rows fn-hrecs$cp fn-hrc-wfp)))))
  (with-local-stobj fn-hrecs$c
    (mv-let (clean rows fn-hrecs$c)
      (mv-let (v fn-hrecs$c)
        (fn-hrc-open-file handle fn-hrecs$c)
        (if v
            (mv nil (make-list (fn-hrs-h-n handle)) fn-hrecs$c)
          (fn-hrc-rows 0 (fn-hrs-h-n handle) (fn-hrs-h-file handle) t nil fn-hrecs$c)))
      (mv clean rows))))

(defun fn-hrs-disk-history (handle)
  ; The committed image's history: the decode, or a fault by name when it
  ; is not clean (history-image-fault: a recovery event; never a silent
  ; value on a served path).  Guard T, the handle checked here: the decode
  ; updates its local stobj, and ACL2's invariant-risk climbs through every
  ; caller whose guard is not T -- up to the host's :program entries, which
  ; would then run their *1* bodies.  It stops at this function.
  (declare (xargs :guard t))
  (if (not (fn-hrs-handlep handle))
      nil
    (mv-let (clean rows)
      (fn-hrs-disk-decode handle)
      (if clean
          rows
        (prog2$ (er hard? 'fn-hrs-disk-history
                       "history-image-fault: the committed history image ~x0 does not decode"
                       handle)
                rows)))))

; -----------------------------------------------------------------------------
; D. The concrete loop is the abstract one's (whatever the ghost), so the
; abstract keystones (`fn-hrecs-get-is-nth') carry over to the decode.

(defthm fn-hrc-get-is-hrecs-get
  (equal (fn-hrecs-get seq file fuel (cons x fn-hrecs$c))
         (let ((r (fn-hrc-get seq file fuel fn-hrecs$c)))
           (mv (mv-nth 0 r) (mv-nth 1 r) (cons x (mv-nth 2 r)))))
  :hints (("Goal" :induct (fn-hrc-get seq file fuel fn-hrecs$c)
           :in-theory (disable fn-hrc-at fn-hrc-fill fn-hrc-phys fn-hrecs$cp fn-hrc-wfp fn-hrc-fill-shape fn-hrs-fill-pgs
                               fn-pgs-fill-realize-is-page-words))))

(defthm fn-hrc-get-keeps
  (implies (and (true-listp h) (fn-hrc-wfp fn-hrecs$c)
                (fn-hrecs-faithful (cons h fn-hrecs$c)) (fn-hrecs-disk-faithful file (cons h fn-hrecs$c)) (natp seq))
           (let ((r (fn-hrc-get seq file fuel fn-hrecs$c)))
             (and (fn-hrc-wfp (mv-nth 2 r))
                  (fn-hrecs-faithful (cons h (mv-nth 2 r)))
                  (fn-hrecs-disk-faithful file (cons h (mv-nth 2 r)))
                  (implies (equal (mv-nth 0 r) :ok)
                           (equal (mv-nth 1 r) (if (< seq (len h)) (list :ok (nth seq h)) (list :refused :seq)))))))
  :hints (("Goal" :use ((:instance fn-hrecs-get-is-nth (st (cons h fn-hrecs$c))))
           :in-theory (e/d (fn-hrecs-list) (fn-hrecs-get-is-nth fn-hrecs-get fn-hrc-get fn-hrecs-faithful fn-hrecs-disk-faithful fn-hrc-wfp)))))

(defthm fn-hrc-rows-not-ok
  (implies (not ok) (not (mv-nth 0 (fn-hrc-rows i n file ok acc fn-hrecs$c))))
  :hints (("Goal" :induct (fn-hrc-rows i n file ok acc fn-hrecs$c) :in-theory (disable fn-hrc-get fn-hrc-vlen))))

(defthm fn-hrc-rows-len
  (equal (len (mv-nth 1 (fn-hrc-rows i n file ok acc fn-hrecs$c)))
         (+ (len acc) (nfix (- (nfix n) (nfix i)))))
  :hints (("Goal" :induct (fn-hrc-rows i n file ok acc fn-hrecs$c) :in-theory (disable fn-hrc-get fn-hrc-vlen))))

(defthm fn-hrs-take-nthcdr-step
  (implies (and (natp i) (natp n) (< i n) (<= n (len h)))
           (equal (take (- n i) (nthcdr i h))
                  (cons (nth i h) (take (- n (+ 1 i)) (nthcdr (+ 1 i) h)))))
  :hints (("Goal" :in-theory (enable take nthcdr nth))))

(defthm fn-hrs-take-zero (equal (take 0 x) nil) :hints (("Goal" :in-theory (enable take))))
(defthm fn-hrc-rows-is-take
  (implies (and (true-listp h) (fn-hrc-wfp fn-hrecs$c)
                (fn-hrecs-faithful (cons h fn-hrecs$c)) (fn-hrecs-disk-faithful file (cons h fn-hrecs$c))
                (natp i) (natp n) (<= i n) (<= n (len h))
                (mv-nth 0 (fn-hrc-rows i n file ok acc fn-hrecs$c)))
           (equal (mv-nth 1 (fn-hrc-rows i n file ok acc fn-hrecs$c))
                  (revappend acc (take (- n i) (nthcdr i h)))))
  :hints (("Goal" :induct (fn-hrc-rows i n file ok acc fn-hrecs$c)
           :in-theory (disable fn-hrc-get fn-hrc-vlen fn-hrecs-faithful fn-hrecs-disk-faithful fn-hrc-wfp take nthcdr fn-hrs-take-nthcdr-step))
          ("Subgoal *1/2" :use ((:instance fn-hrc-get-keeps (seq i) (fuel (fn-hrc-vlen fn-hrecs$c))) (:instance fn-hrs-take-nthcdr-step)))))

(defthm fn-hrc-rows-true-listp
  (true-listp (mv-nth 1 (fn-hrc-rows i n file ok acc fn-hrecs$c)))
  :hints (("Goal" :induct (fn-hrc-rows i n file ok acc fn-hrecs$c) :in-theory (disable fn-hrc-get fn-hrc-vlen))))

; -----------------------------------------------------------------------------
; E. What the decode is.

(defthm fn-hrc-wfp-of-create
  (fn-hrc-wfp (create-fn-hrecs$c)))

(defthm fn-hrc-open-file-fields
  (let ((r (fn-hrc-open-file handle fn-hrecs$c)))
    (implies (not (mv-nth 0 r))
             (and (equal (fn-hrc-nimg (mv-nth 1 r)) (fn-hrs-h-n handle))
                  (equal (fn-hrc-lo (mv-nth 1 r)) 0)
                  (equal (fn-hrc-hi (mv-nth 1 r)) 0))))
  :hints (("Goal" :in-theory (disable fn-hrs-open-pgs fn-hrecs$cp fn-hrs-h-n))))

(defun-nx fn-hrs-disk-holds (handle h)
  ; The page file holds H's image at the addresses the committed tables
  ; name: the handle's open lands, and over the state it leaves the
  ; concrete holds H (`fn-hrecs-faithful': the header is H's image's, its
  ; count H's length) and the page file holds H's image page at the
  ; address the loaded table names for every page (`fn-hrecs-disk-faithful').
  (let ((r (fn-hrc-open-file handle (create-fn-hrecs$c))))
    (and (not (mv-nth 0 r))
         (fn-hrecs-faithful (cons h (mv-nth 1 r)))
         (fn-hrecs-disk-faithful (fn-hrs-h-file handle) (cons h (mv-nth 1 r))))))

(defthm fn-hrs-len-when-nthcdr-nil
  (implies (and (true-listp h) (natp k) (<= k (len h)) (not (nthcdr k h)))
           (equal (len h) k))
  :hints (("Goal" :in-theory (enable nthcdr)))
  :rule-classes nil)

(defthm fn-hrs-rel-len
  (implies (and (fn-hrs-rel h c) (fn-hrc-wfp c) (equal (fn-hrc-lo c) 0) (equal (fn-hrc-hi c) 0))
           (and (true-listp h) (equal (len h) (fn-hrc-nimg c))))
  :hints (("Goal" :in-theory (enable fn-hrs-rel fn-hrc-sfx-list)
           :use ((:instance fn-hrs-len-when-nthcdr-nil (k (fn-hrc-nimg c))))))
  :rule-classes nil)

; KEYSTONE (the lazy decode): when the page file holds H's image at the
; addresses the committed tables name, and the decode is clean, the
; history the handle names is H.
(defthm fn-hrs-disk-history-is-image
  (implies (and (fn-hrs-handlep handle) (fn-hrs-disk-holds handle h) (mv-nth 0 (fn-hrs-disk-decode handle)))
           (equal (fn-hrs-disk-history handle) h))
  :hints (("Goal" :in-theory (e/d (fn-hrecs-faithful) (fn-hrc-open-file fn-hrc-rows fn-hrecs$cp fn-hrc-wfp fn-hrs-rel
                                                      fn-hrecs-disk-faithful create-fn-hrecs$c))
           :use ((:instance fn-hrs-rel-len (c (mv-nth 1 (fn-hrc-open-file handle (create-fn-hrecs$c)))))
                 (:instance fn-hrc-rows-is-take (i 0) (n (fn-hrs-h-n handle)) (file (fn-hrs-h-file handle)) (ok t) (acc nil)
                            (fn-hrecs$c (mv-nth 1 (fn-hrc-open-file handle (create-fn-hrecs$c)))))))))

(defthm fn-hrs-len-make-list-ac
  (equal (len (make-list-ac n val ac)) (+ (nfix n) (len ac))))
(defthm fn-hrs-disk-history-len
  (implies (fn-hrs-handlep handle)
           (equal (len (fn-hrs-disk-history handle)) (fn-hrs-h-n handle)))
  :hints (("Goal" :in-theory (disable fn-hrc-open-file fn-hrc-rows create-fn-hrecs$c))))

(defthm fn-hrs-true-listp-make-list-ac (equal (true-listp (make-list-ac n val ac)) (true-listp ac)))
(defthm fn-hrs-true-listp-disk-history
  (true-listp (fn-hrs-disk-history handle))
  :hints (("Goal" :in-theory (disable fn-hrc-open-file fn-hrc-rows create-fn-hrecs$c))))

(defthm fn-hrs-true-listp-disk-history-tp
  (true-listp (fn-hrs-disk-history handle))
  :rule-classes :type-prescription)

(in-theory (disable fn-hrs-disk-history fn-hrs-disk-decode fn-hrc-open-file fn-hrc-rows fn-hrc-get
                    fn-hrs-open-pgs fn-hrs-load-dir fn-hrs-load-tables fn-hrs-fill-run fn-hrs-size-image
                    fn-hrs-handlep))
