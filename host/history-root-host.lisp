; The native resident P3 root's actual owner association and retained credit.
; Internal publishers supply only results of the guarded concrete producers.
; Logical Store/view authority remains the canonical owner installer.
(in-package "ACL2")
; The sibling edge is an include-book (the account-*/index-* discipline),
; not an `ld': certify-book refuses an ld (LD-FN is not an embedded event
; form).  In a session that ld'd owner-host earlier the include is
; redundant and loads nothing.
(include-book "owner-host")
(include-book "../books/history-root-credit")
(include-book "../books/history-root-work-credit")
(include-book "../books/history-paged-adopt")

(defun fn-owner-hroot-get (generation state)
  (declare (xargs :stobjs state :mode :program))
  (cdr (assoc-equal generation
    (and (boundp-global 'fn-owner-history-roots state)
         (f-get-global 'fn-owner-history-roots state)))))
(defun fn-owner-hroot-put (generation row state)
  (declare (xargs :stobjs state :mode :program))
  (f-put-global 'fn-owner-history-roots
    (fn-hroot-table-put (and (boundp-global 'fn-owner-history-roots state)
                             (f-get-global 'fn-owner-history-roots state))
                        generation row) state))
;; The refresh's word as ACL2 classifies it (books/history-root-credit.lisp
;; fn-hroot-refresh-status), held for `status' and `health' to render
;; (books/history-root-status.lisp fn-hrs-line).  It lives in the history-root
;; table (fn-owner-history-roots) under the reserved key :last-refresh
;; (fn-hroot-table-note), not in a global of its own.  Every word the host got
;; is noted: a building/installed word clears a refusal, a refusal or an
;; unrecognised word replaces it.  Returns the status for the host's log.
(defun fn-owner-hroot-note (word state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((table (fn-hroot-table-note (fn-owner-history-root-table state) word))
         (state (f-put-global 'fn-owner-history-roots table state)))
    (value (fn-hroot-table-status table))))

(definterface fn-owner-hroot-note :class :program)

(defun fn-owner-hroot-resize (generation amount state)
  (declare (xargs :stobjs state :mode :program))
  (let ((r (fn-mcr-hroot-resize (fn-owner-credits state) (fn-hroot-credit-key generation) amount)))
    (if (eq (car r) :ok)
        (let ((state (fn-owner-put-credits (cadr r) state)))
          (mv :funded state))
      (mv r state))))

(definterface fn-owner-hroot-resize :class :program)
;; The per-event decode transient of a generation under construction: an ops
;; credit against the article pool (never the history-root reserve), drawn
;; before the decode and set back to 0 after it.  Refused by name,
;; :memory-budget-exhausted, when the pool is short.
(defun fn-owner-hroot-transient (generation amount state)
  (declare (xargs :stobjs state :mode :program))
  (let ((r (fn-mcr-resize (fn-owner-credits state) (cons :history-root-event generation) amount)))
    (if (eq (car r) :ok)
        (let ((state (fn-owner-put-credits (cadr r) state)))
          (mv :funded state))
      (mv r state))))

(definterface fn-owner-hroot-transient :class :program)
(defun fn-owner-hroot-release-credit (generation state)
  (declare (xargs :stobjs state :mode :program))
  (let ((r (fn-mcr-resize (fn-owner-credits state) (cons :history-root-tail generation) 0)))
    (if (not (eq (car r) :ok)) (mv r state)
      (let ((state (fn-owner-put-credits (cadr r) state)))
        (mv-let (word state) (fn-owner-hroot-transient generation 0 state)
          (if (not (eq word :funded)) (mv word state)
            (fn-owner-hroot-resize generation 0 state)))))))
(defun fn-owner-hroot-begin (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((bound (boundp-global 'fn-owner-history-root-counter state))
         (old (and bound (f-get-global 'fn-owner-history-root-counter state))))
    (if (and bound (not (natp old))) (value '(:refused :history-root-counter))
      ; ACL2 decides the funding and its word (books/history-root-credit.lisp
      ; fn-hroot-begin-word: :funded, or (:refused REASON ASK ROOM) with the
      ; resize's own reason); the ledger changes only on :funded.
      (let* ((generation (+ 1 (if bound old 0)))
             (credits (fn-owner-credits state))
             (word (fn-hroot-begin-word credits generation)))
        (if (not (eq word :funded)) (value word)
          (let* ((state (fn-owner-put-credits (fn-hroot-begin-ledger credits generation) state))
                 (state (f-put-global 'fn-owner-history-root-counter generation state))
                 (state (fn-owner-hroot-put generation (list :building nil nil) state)))
            (value (list :building generation))))))))

(definterface fn-owner-hroot-begin :class :program)
(defun fn-owner-hroot-abandon-word (generation state)
  (declare (xargs :stobjs state :mode :program))
  (let ((row (fn-owner-hroot-get generation state)))
    (value (if (and (eq (car row) :building) (not (caddr row)))
               :ready :history-root-held))))

(definterface fn-owner-hroot-abandon-word :class :program)
(defun fn-owner-hroot-abandon (generation state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (erp word state) (fn-owner-hroot-abandon-word generation state)
    (declare (ignore erp))
    (if (not (eq word :ready))
        (value :history-root-held)
      (mv-let (word state) (fn-owner-hroot-release-credit generation state)
        (if (not (eq word :funded)) (value word)
          (let ((state (fn-owner-hroot-put generation nil state)))
            (value :released)))))))

(definterface fn-owner-hroot-abandon :class :program)
(defun fn-owner-hroot-current (state)
  (declare (xargs :stobjs state :mode :program))
  (and (boundp-global 'fn-owner-history-root-current state)
       (f-get-global 'fn-owner-history-root-current state)))
(defun fn-owner-hroot-frontier (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((owner (fn-owner-core state)))
    (list (fn-sf-records-count (fn-sn-files (fn-own-store owner)))
          (fn-sf-frontier (fn-sn-files (fn-own-store owner)))
          (fn-own-config owner)
          (and (boundp-global 'fn-owner-history-source-counter state)
               (f-get-global 'fn-owner-history-source-counter state)))))
; One producer row at a time, after the established history synchronization.
; The native captures the actual history handle under the same owner gate.
(defun fn-owner-hroot-row (ordinal source-incarnation fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (mv-let (fn-hist state) (fn-host-hist-sync (fn-owner-store state) fn-hist state)
    (let* ((n (fn-hist-count fn-hist))
           (word (cond ((not (equal source-incarnation (nth 3 (fn-owner-hroot-frontier state))))
                        '(:refused :history-source-changed))
                       ((or (not (natp ordinal)) (< n ordinal))
                        '(:refused :history-root-ordinal))
                       ((equal ordinal n) (list :done (fn-owner-hroot-frontier state)))
                       (t (list :event (fn-hist-at ordinal fn-hist)
                                (fn-owner-hroot-frontier state))))))
      (mv nil word fn-hist state))))

(definterface fn-owner-hroot-row :class :program)
(defun fn-owner-hroot-activate (generation count captured-frontier state)
  (declare (xargs :stobjs state :mode :program))
  (let ((row (fn-owner-hroot-get generation state))
        (current (fn-owner-hroot-frontier state)))
    (cond ((not (eq (car row) :building)) (value '(:refused :history-root-state)))
          ((not (and (natp count) (equal count (car current))
                     (equal current captured-frontier))) (value :changed))
          (t
           (let* ((old (fn-owner-hroot-current state))
                  (old-row (and old (fn-owner-hroot-get old state)))
                  (state (if old
                             (fn-owner-hroot-put old (list :retired (cadr old-row)
                                                          (caddr old-row)) state) state))
                  (state (fn-owner-hroot-put generation (list :live current nil) state))
                  (state (f-put-global 'fn-owner-history-root-current generation state)))
             (value (list :installed generation old)))))))

(definterface fn-owner-hroot-activate :class :program)
(defun fn-owner-hroot-pin (physical-generation tail-credit workp fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (let* ((generation (fn-owner-hroot-current state))
         (row (and generation (fn-owner-hroot-get generation state)))
         (bound (boundp-global 'fn-owner-history-root-lease-counter state))
         (old (and bound (f-get-global 'fn-owner-history-root-lease-counter state))))
    (if (or (not (equal physical-generation generation))
            (not (eq (car row) :live)) (and bound (not (natp old))))
        (mv nil '(:refused :history-root-source) fn-hist state)
      (mv-let (fn-hist state) (fn-host-hist-sync (fn-owner-store state) fn-hist state)
        (let* ((token (+ 1 (if bound old 0)))
               (source (list :history-root token generation (fn-hist-count fn-hist)
                             (fn-owner-hroot-frontier state) workp))
               (credit (fn-hroot-reader-resize (fn-owner-credits state)
                          (cons :history-root-lease token) (+ 256 (nfix tail-credit)) workp)))
          (if (not (eq (car credit) :ok)) (mv nil credit fn-hist state)
            (let* ((state (fn-owner-put-credits (cadr credit) state))
                   (state (f-put-global 'fn-owner-history-root-lease-counter token state))
                   (state (fn-owner-hroot-put generation
                            (list :live (cadr row) (acons token source (caddr row))) state)))
              (mv nil source fn-hist state))))))))
; INTERNAL terminal return: native iterator has returned and cleared its handle.
; Cancellation alone never invokes this producer.
(defun fn-owner-hroot-return (source state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((token (cadr source)) (generation (caddr source))
         (row (fn-owner-hroot-get generation state)))
    (if (not (and (eq (car source) :history-root) (equal source (cdr (assoc-equal token (caddr row))))))
        (value :history-root-stale)
      (let* ((read-credit (fn-hroot-reader-resize (fn-owner-credits state)
                                         (cons :history-root-read token) 0 (nth 5 source)))
             (lease-credit (and (eq (car read-credit) :ok)
                               (fn-hroot-reader-resize (cadr read-credit)
                                             (cons :history-root-lease token) 0 (nth 5 source)))))
        (if (not (and (eq (car read-credit) :ok) (eq (car lease-credit) :ok)))
            (value '(:refused :history-root-credit-return))
          (let* ((state (fn-owner-put-credits (cadr lease-credit) state))
                 (state (fn-owner-hroot-put generation
                          (list (car row) (cadr row) (remove1-assoc-equal token (caddr row))) state)))
            (value :returned)))))))

(definterface fn-owner-hroot-return :class :program)
; INTERNAL pre-destruction word. The caller holds the owner gate through
; physical disposal and the existing credit return. Retired generations
; cannot acquire new leases, and an issued lease prevents this word.
(defun fn-owner-hroot-retire-word (generation state)
  (declare (xargs :stobjs state :mode :program))
  (let ((row (fn-owner-hroot-get generation state)))
    (value (if (and (eq (car row) :retired) (null (caddr row)))
               :ready :history-root-held))))

(definterface fn-owner-hroot-retire-word :class :program)

(defun fn-owner-hroot-retire (generation state)
  (declare (xargs :stobjs state :mode :program))
  (let ((row (fn-owner-hroot-get generation state)))
    (if (not (and (eq (car row) :retired) (null (caddr row))))
        (value :history-root-held)
      (mv-let (word state) (fn-owner-hroot-release-credit generation state)
        (if (not (eq word :funded)) (value word)
          (let ((state (fn-owner-hroot-put generation nil state)))
            (value :released)))))))

(definterface fn-owner-hroot-retire :class :program)

(defun fn-owner-hroot-read-plan (source ordinal state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((row (fn-owner-hroot-get (caddr source) state))
         (owned (cdr (assoc-equal (cadr source) (caddr row)))))
    (value
      (cond ((not (and (eq (car source) :history-root) (equal owned source)))
             '(:refused :history-root-stale))
            ((not (and (natp ordinal) (< ordinal (cadddr source))))
             '(:refused :history-root-ordinal))
            (t (list :read (caddr source) ordinal))))))

(definterface fn-owner-hroot-read-plan :class :program)

; Every replacement of canonical fn-hist changes this ACL2 incarnation before
; the host installs its new pointer. A same-count rewrite cannot pass a stale
; candidate's captured frontier. Pins on the retired root remain registered.
(defun fn-owner-hroot-detach (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((bound (boundp-global 'fn-owner-history-source-counter state))
         (old (and bound (f-get-global 'fn-owner-history-source-counter state)))
         (generation (fn-owner-hroot-current state))
         (row (and generation (fn-owner-hroot-get generation state))))
    (if (and bound (not (natp old))) (value '(:refused :history-source-counter))
      (let* ((state (f-put-global 'fn-owner-history-source-counter (+ 1 (if bound old 0)) state))
             (state (if generation (fn-owner-hroot-put generation
                            (list :retired (cadr row) (caddr row)) state) state))
             (state (f-put-global 'fn-owner-history-root-current nil state)))
        (value (list :detached generation))))))

(definterface fn-owner-hroot-detach :class :program)

; A snapshot borrows the owner's existing work reserve for its retained
; tail and decoded rows; ordinary streaming/reclaim keeps its ops funding.
; Work credit is per lease, so mixed readers never reinterpret each other's
; grants and the last snapshot return returns exactly its own reservation.
(defun fn-owner-hroot-pin-funded (physical-generation workp fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program))
  (if (not (and (posp physical-generation)
                (equal physical-generation (fn-owner-hroot-current state))))
      (mv nil '(:refused :history-root-source) fn-hist state)
    (mv-let (bytes fn-hist state) (fn-owner-record-octets fn-hist state)
      (if workp
          (fn-owner-hroot-pin physical-generation (* 16 bytes) t fn-hist state)
        (let ((credit (fn-mcr-resize (fn-owner-credits state)
                                    (cons :history-root-tail physical-generation) (* 16 bytes))))
          (if (not (eq (car credit) :ok)) (mv nil credit fn-hist state)
            (let ((state (fn-owner-put-credits (cadr credit) state)))
              (fn-owner-hroot-pin physical-generation 0 nil fn-hist state))))))))

(definterface fn-owner-hroot-pin-funded :class :program)

(defun fn-owner-hroot-frontier-value (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-owner-hroot-frontier state)))

(definterface fn-owner-hroot-frontier-value :class :program)

; A resize grant lives in the reserved component; both components remain
; retained until the reader releases the rows, so accumulate their sum.
(defun fn-owner-hroot-read-owned (source state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-mcr-credit-of (cons :history-root-read (cadr source))
                            (fn-mcr-ops (fn-owner-credits state)))))

(definterface fn-owner-hroot-read-owned :class :program)
(defun fn-owner-hroot-read-fund (source amount state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((row (fn-owner-hroot-get (caddr source) state))
         (owned (cdr (assoc-equal (cadr source) (caddr row)))))
    (if (not (and (eq (car source) :history-root) (equal source owned) (natp amount)))
        (value '(:refused :history-root-stale))
      (let ((r (fn-hroot-reader-resize (fn-owner-credits state)
                              (cons :history-root-read (cadr source)) amount (nth 5 source))))
        (if (not (eq (car r) :ok)) (value r)
          (let ((state (fn-owner-put-credits (cadr r) state)))
            (value :funded)))))))

(definterface fn-owner-hroot-read-fund :class :program)

; Reclaim has already prepared its page-backed history candidate. Loading
; its fresh catalog must not also allocate an all-tail duplicate of history.
; The load is chunked (lane reclaim, PRF-1315): the keyed clear, then the
; rebuilt capture's own records a chunk per call; together they are the
; keyed open over the whole list (books/reclaim-chunked-seal.lisp KEYSTONE
; fn-rcw-load-chunks-keyed-is-keyed-load).  Availability is each predicted
; row's decided facts (fn-orcs-held-of), never an arena read.
(defun fn-owner-orcp-load-catalog-begin (key fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (let ((fn-cat (fn-cat-clear-keyed key fn-cat)))
    (mv :cleared fn-cat)))

(definterface fn-owner-orcp-load-catalog-begin :class :program)

(defun fn-owner-orcp-load-catalog-chunk (rows view-index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :mode :program))
  (let ((fn-cat (fn-sca-load-held-available-from rows view-index fn-arena fn-cat)))
    (mv :loaded fn-cat)))

(definterface fn-owner-orcp-load-catalog-chunk :class :program
  :keystones ((fn-rcw-load-chunks-keyed-is-keyed-load
               :step-of fn-rcw-load-chunks fn-sca-load-held-available-from)))
