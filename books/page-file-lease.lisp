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
                            (cons (cons token (list demand :file-pin nil))
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
