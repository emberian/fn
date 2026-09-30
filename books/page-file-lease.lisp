; A captured checkpoint owns one exact physical incarnation through its
; repeated logical scans. This is not an arena-generation pin or a worker.
; One descriptor/retention credit bounds pin rows jointly with open files.
(in-package "ACL2")
(include-book "page-read-ledger")

(defun fn-prf-acquire (ledger file demand)
  (declare (xargs :guard t))
  (let* ((budget (fn-prl-nth 0 ledger))
         (charged (fn-prl-nth 1 ledger))
         (next (fn-prl-nth 2 ledger)))
    (mv-let (word next1 charged1)
      (if (and (posp file)
               (equal (fn-prl-nth 1
                       (cdr (fn-prl-binding (list :incarnation file)
                                            (fn-prl-nth 3 ledger)))) :incarnation)
               (fn-prs-vectorp demand)
               (equal (fn-prl-nth 2 demand) 1)
               (equal (fn-prl-nth 3 demand) 0)
               (equal (fn-prl-nth 4 demand) 1))
          (fn-prs-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                        charged next (fn-prl-nth 4 budget) demand)
        (mv :invalid-file-pin-demand next charged))
      (if (not (equal word :admitted)) (mv word nil ledger)
        (let ((token (list :file-pin next file)))
          (mv :admitted token
              (fn-prl-build budget charged1 next1
                            (cons (cons token (list demand :file-pin nil 0))
                                  (fn-prl-nth 3 ledger))
                            (fn-prl-nth 4 ledger))))))))

(defun fn-prf-file (ledger token)
  (declare (xargs :guard t))
  (let ((binding (fn-prl-binding token (fn-prl-nth 3 ledger))))
    (if (and (equal (fn-prl-nth 0 token) :file-pin)
             (equal (fn-prl-nth 1 (cdr binding)) :file-pin))
        (fn-prl-nth 2 token) nil)))

(defun fn-prf-release (ledger token)
  (declare (xargs :guard t))
  (let* ((binding (fn-prl-binding token (fn-prl-nth 3 ledger)))
         (row (if (consp binding) (cdr binding) nil))
         (charged (fn-prl-nth 1 ledger))
         (demand (fn-prl-nth 0 row)))
    (if (not (and (fn-prf-file ledger token)
                  (true-listp charged) (true-listp demand)))
        (mv :stale ledger)
      (mv :released
          (fn-prl-build (fn-prl-nth 0 ledger)
                        (fn-prs-release-reusable charged demand)
                        (fn-prl-nth 2 ledger)
                        (fn-prl-remove token (fn-prl-nth 3 ledger))
                        (fn-prl-nth 4 ledger))))))

(defthm fn-prf-acquire-preserves-pool-funding
  (implies (equal (mv-nth 0 (fn-prf-acquire ledger file demand)) :admitted)
           (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                           '(0 0 0 0 0)
                           (fn-prl-nth 1 (mv-nth 2 (fn-prf-acquire ledger file demand)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prf-acquire fn-prl-nth fn-prl-build)
           :use ((:instance fn-prs-issue-preserves-static-rescue
                            (budget (fn-prl-nth 0 ledger))
                            (used (fn-prl-baseline ledger))
                            (rescue '(0 0 0 0 0))
                            (charged (fn-prl-nth 1 ledger))
                            (next (fn-prl-nth 2 ledger))
                            (limit (fn-prl-nth 4 (fn-prl-nth 0 ledger))))))))

(defthm fn-prf-acquired-file-is-held
  (implies (equal (mv-nth 0 (fn-prf-acquire ledger file demand)) :admitted)
           (equal (fn-prl-close-preview
                   (mv-nth 2 (fn-prf-acquire ledger file demand)) file)
                  :read-file-held))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prf-acquire fn-prl-nth fn-prl-build
                                    fn-prl-close-preview fn-prl-file-heldp))))

(defthm fn-prf-release-preserves-permanent-baseline
  (equal (fn-prl-baseline (mv-nth 1 (fn-prf-release ledger token)))
         (fn-prl-baseline ledger))
  :hints (("Goal" :in-theory (enable fn-prf-release fn-prl-baseline fn-prl-build fn-prl-nth))))

 ; Physical placement only. Authentication and logical root/epoch matching
; belong to the bounded source reader. BASE already skips the FNSI wrapper.
; The selected native pread ABI has a signed 64-bit offset and length16KiB.
(defun fn-prf-page-placement (ledger token request base)
  (declare (xargs :guard t))
  (let ((file (fn-prf-file ledger token))
        (page (fn-prl-nth 5 request))
        (offset (fn-prl-nth 6 request)))
    (if (and file (natp base) (true-listp request) (equal (len request) 9)
             (equal (fn-prl-nth 0 request) :read-page)
             (equal (fn-prl-nth 1 request) (fn-prl-nth 1 token))
             (natp (fn-prl-nth 2 request)) (natp (fn-prl-nth 3 request))
             (member-eq (fn-prl-nth 4 request) '(:directory :table :data))
             (natp page) (natp offset) (equal offset (* 16384 page))
             (equal (fn-prl-nth 7 request) 16384)
             (natp (fn-prl-nth 8 request))
             (<= (+ base offset 16384) 9223372036854775807))
        (mv :placed file (+ base offset) 16384)
      (mv :invalid-page-placement nil 0 0))))

(defthm fn-prf-page-placement-by-definition
  (implies (equal (mv-nth 0 (fn-prf-page-placement ledger token request base)) :placed)
           (and (equal (mv-nth 1 (fn-prf-page-placement ledger token request base))
                       (fn-prf-file ledger token))
                (equal (fn-prl-nth 1 request) (fn-prl-nth 1 token))
                (equal (mv-nth 2 (fn-prf-page-placement ledger token request base))
                       (+ base (fn-prl-nth 6 request)))
                (equal (mv-nth 3 (fn-prf-page-placement ledger token request base)) 16384)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prf-page-placement))))

(in-theory (disable fn-prf-acquire fn-prf-file fn-prf-release fn-prf-page-placement))

; The syscall has actually returned. This projects only an exact live raw
; buffer lease for the unchanged request. Authentication remains the reader's
; responsibility; short/error results retain the same borrow and charge.
(defun fn-prf-read-result (ledger root request base buffer-token got io-status)
  (declare (xargs :guard t))
  (mv-let (word file offset count)
    (fn-prf-page-placement ledger root request base)
    (let ((binding (fn-prl-binding buffer-token (fn-prl-nth 3 ledger))))
      (if (not (and (equal word :placed) (equal count 16384)
                    (true-listp buffer-token) (equal (len buffer-token) 5)
                    (equal (fn-prl-nth 0 buffer-token) :discovery)
                    (natp (fn-prl-nth 1 buffer-token))
                    (equal (fn-prl-nth 2 buffer-token) file)
                    (equal (fn-prl-nth 3 buffer-token) offset)
                    (equal (fn-prl-nth 4 buffer-token) count)
                    (equal (fn-prl-nth 1 (cdr binding)) :discovery)))
          (mv :stale-read nil 0 :stale)
        (mv :read-result (fn-prl-nth 1 buffer-token)
            (if (and (natp got) (<= got count)) got 0)
            (cond ((not (and (equal io-status :ok) (natp got) (<= got count))) :io-error)
                  ((equal got count) :read-ok)
                  (t :short-read)))))))

(defthm fn-prf-read-result-authority-by-definition
  (implies (equal (mv-nth 3 (fn-prf-read-result ledger root request base buffer-token got io-status)) :read-ok)
    (and (equal (mv-nth 0 (fn-prf-read-result ledger root request base buffer-token got io-status)) :read-result)
         (equal (mv-nth 1 (fn-prf-read-result ledger root request base buffer-token got io-status))
                (fn-prl-nth 1 buffer-token))
         (equal (mv-nth 2 (fn-prf-read-result ledger root request base buffer-token got io-status)) 16384)
         (equal got 16384) (equal io-status :ok)
         (equal (fn-prl-nth 1 (cdr (fn-prl-binding buffer-token (fn-prl-nth 3 ledger)))) :discovery)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-prf-read-result fn-prf-page-placement))))

(defun fn-prf-ticket (ledger token)
  (declare (xargs :guard t))
  (and (true-listp token) (equal (len token) 3)
       (natp (fn-prl-nth 1 token)) (posp (fn-prl-nth 2 token))
       (fn-prf-file ledger token) (fn-prl-nth 1 token)))

; Per-root spent discovery census. The atomic pin-read caller records this
; immediately after successful issuer admission, before allocation or pread.
; Legacy binding lookup/remove is profile-bounded scan/copy, not O(1).
(defun fn-prf-issued-count (ledger root)
  (declare (xargs :guard t))
  (let ((row (cdr (fn-prl-binding root (fn-prl-nth 3 ledger)))))
    (if (and (fn-prf-file ledger root) (natp (fn-prl-nth 3 row)))
        (mv :count (fn-prl-nth 3 row))
      (mv :stale-root 0))))
(defun fn-prf-note-admitted-read (ledger root request buffer-token)
  (declare (xargs :guard t))
  (let* ((rows (fn-prl-nth 3 ledger))
         (root-row (cdr (fn-prl-binding root rows)))
         (buffer-row (cdr (fn-prl-binding buffer-token rows))))
    (if (not (and (fn-prf-file ledger root) (natp (fn-prl-nth 3 root-row))
                  (equal (fn-prl-nth 0 buffer-token) :discovery)
                  (equal (fn-prl-nth 1 buffer-row) :discovery)
                  (equal (fn-prl-nth 2 buffer-token) (fn-prf-file ledger root))
                  (equal (fn-prl-nth 1 request) (fn-prl-nth 1 root))
                  (null (fn-prl-nth 3 buffer-row))))
        (mv :unrecorded ledger)
      (mv :recorded
          (fn-prl-build (fn-prl-nth 0 ledger) (fn-prl-nth 1 ledger)
                        (fn-prl-nth 2 ledger)
                        (cons (cons root (list (fn-prl-nth 0 root-row) :file-pin nil
                                               (+ 1 (nfix (fn-prl-nth 3 root-row)))))
                              (cons (cons buffer-token
                                          (list (fn-prl-nth 0 buffer-row) :discovery
                                                (fn-prl-nth 2 buffer-row)
                                                (list root request :issued)))
                                    (fn-prl-remove buffer-token (fn-prl-remove root rows))))
                        (fn-prl-baseline ledger))))))
(defthm fn-prf-recording-preserves-issued-pool-charge
  (equal (fn-prl-nth 1 (mv-nth 1 (fn-prf-note-admitted-read ledger root request buffer-token)))
         (fn-prl-nth 1 ledger))
  :hints (("Goal" :in-theory (e/d (fn-prf-note-admitted-read fn-prl-build fn-prl-nth)
                                (fn-prf-file fn-prl-binding fn-prl-remove)))))
(defthm fn-prf-recording-preserves-spent-identity-counter
  (equal (fn-prl-nth 2 (mv-nth 1 (fn-prf-note-admitted-read ledger root request buffer-token)))
         (fn-prl-nth 2 ledger))
  :hints (("Goal" :in-theory (e/d (fn-prf-note-admitted-read fn-prl-build fn-prl-nth)
                                (fn-prf-file fn-prl-binding fn-prl-remove)))))
