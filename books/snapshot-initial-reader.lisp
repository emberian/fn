; Actual history reader constructor entry under retained INITIAL custody.
; No whole-reader RETURN follows from page settlement or a host Boolean.
(in-package "ACL2")
(include-book "snapshot-initial-custody")
(include-book "history-records-disk")
(include-book "history-auth-reader-source")

(defun fn-snir-initial (ledger maintenance)
 (declare (xargs :guard t))
 (fn-prl-nth 3 (cdr (fn-prl-binding maintenance (fn-prl-nth 3 ledger)))))

(defun fn-snir-sourcep (ledger source maintenance page-source root-ticket)
 (declare (xargs :guard t))
 (let* ((initial (fn-snir-initial ledger maintenance))
        (descriptor (fn-prl-nth 2 initial))
        (context (fn-prl-nth 3 initial))
        (roles (fn-prl-nth 6 initial))
        (held-root (fn-sni-role-entry :source-root roles))
        (root-token (fn-prl-nth 2 held-root))
        (root-row (cdr (fn-prl-binding root-token (fn-prl-nth 3 ledger))))
        (turn (fn-sni-role-entry :allocation-turn roles))
        (reader (fn-sni-role-entry :reader roles))
        (pair (fn-prl-nth 1 page-source)))
  (and (fn-sni-livep ledger source maintenance)
       (fn-omk-tokenp page-source)
       (natp root-ticket)
       (natp (fn-prl-nth 3 page-source))
       (equal (fn-prl-nth 0 page-source) (fn-prl-nth 1 context))
       (equal (fn-prl-nth 0 pair) (fn-prl-nth 1 source))
       (equal (fn-prl-nth 1 pair) (fn-prl-nth 6 descriptor))
       (< (fn-prl-nth 3 page-source) (nfix (fn-prl-nth 3 context)))
       (equal (fn-prl-nth 1 held-root) :held)
       (equal (fn-prl-nth 0 root-token) :file-pin)
       (equal (fn-prl-nth 1 root-token) root-ticket)
       (equal (fn-prl-nth 1 root-row) :file-pin)
       (equal (fn-prl-nth 2 root-token) (fn-hrs-h-file (fn-prl-nth 5 context)))
       (equal (fn-prl-nth 1 turn) :held)
       (equal (fn-prl-nth 2 turn) (list :initial-constructor maintenance source))
       ; A constructor is issued once per attempt. Refuse re-entry before
       ; invoking the actual reader constructor, not after its cursor and
       ; binding have already been allocated and a role claim then fails.
       (equal (fn-prl-nth 1 reader) :reserved))))

(defun fn-snir-begin (ledger source maintenance page-source root-ticket)
 (declare (xargs :guard t))
 (if (not (fn-snir-sourcep ledger source maintenance page-source root-ticket))
     (mv '(:retained :initial-reader-source) nil nil nil ledger)
   (let* ((context (fn-prl-nth 3 (fn-snir-initial ledger maintenance)))
          (root (fn-hrs-h-rec (fn-prl-nth 5 context))))
    (mv-let (word cursor binding)
     (fn-hsr-source-begin root page-source root-ticket maintenance)
     (if (not (equal word :idle)) (mv word nil nil nil ledger)
       (let ((token (list :initial-reader maintenance source root-ticket binding)))
        (mv-let (claimed next)
         (fn-sni-role-claim ledger maintenance source :reader token)
         (if (not (equal claimed :claimed))
             (mv (list :retained claimed) nil nil nil ledger)
           (mv :reader token cursor binding next)))))))))

(local
 (defthm fn-snir-source-begin-car-never-reader-word
  (not (equal (car (fn-hsr-source-begin root page-source root-ticket maintenance)) :reader))
  :hints (("Goal" :in-theory
            (e/d (fn-hsr-source-begin fn-hsr-auth-begin)
                 (fn-omk-tokenp fn-omk-at fn-hsr-rootp fn-hsr-field
                  fn-hsr-io-begin pgs-x-ntables pgs-ptab-run-pages))))))

(local
 (defthm fn-snir-claimed-role-list-has-held-token
  (implies (equal (mv-nth 0 (fn-sni-claim-role-list roles role token)) :claimed)
   (equal (fn-sni-role-entry role (mv-nth 1 (fn-sni-claim-role-list roles role token)))
          (list role :held token)))
  :hints (("Goal" :induct (fn-sni-claim-role-list roles role token)
           :in-theory (enable fn-sni-claim-role-list fn-sni-role-entry fn-prl-nth)))))

(local
 (defthm fn-snir-role-claim-retains-held-token
  (implies (equal (mv-nth 0 (fn-sni-role-claim ledger maintenance source role token)) :claimed)
   (equal (fn-sni-role-entry role
           (fn-prl-nth 6 (fn-snir-initial
                         (mv-nth 1 (fn-sni-role-claim ledger maintenance source role token)) maintenance)))
          (list role :held token)))
  :hints (("Goal" :in-theory
           (e/d (fn-sni-role-claim fn-snir-initial fn-prl-build fn-prl-binding fn-pmn-row fn-prl-nth)
                (fn-sni-claim-role-list fn-sni-livep fn-sni-role-entry))))))

; This theorem speaks about all FIVE actual returned values, including the
; real source-reader call and the same ledger's retained custody. It does
; not establish a native holder, array capacity or allocator observation.
(defthm fn-snir-begin-captures-actual-reader-and-custody
 (implies (equal (mv-nth 0 (fn-snir-begin ledger source maintenance page-source root-ticket)) :reader)
  (let* ((initial (fn-snir-initial ledger maintenance))
         (context (fn-prl-nth 3 initial))
         (actual (fn-hsr-source-begin (fn-hrs-h-rec (fn-prl-nth 5 context))
                                      page-source root-ticket maintenance))
         (result (fn-snir-begin ledger source maintenance page-source root-ticket))
         (next (mv-nth 4 result))
         (token (mv-nth 1 result)))
   (and (fn-snir-sourcep ledger source maintenance page-source root-ticket)
        (equal (mv-nth 0 actual) :idle)
        (equal token (list :initial-reader maintenance source root-ticket (mv-nth 2 actual)))
        (equal (mv-nth 2 result) (mv-nth 1 actual))
        (equal (mv-nth 3 result) (mv-nth 2 actual))
        (fn-sni-livep next source maintenance)
        (equal (fn-prl-nth 0 next) (fn-prl-nth 0 ledger))
        (equal (fn-prl-nth 1 next) (fn-prl-nth 1 ledger))
        (equal (fn-prl-nth 2 next) (fn-prl-nth 2 ledger))
        (equal (fn-prl-nth 4 next) (fn-prl-nth 4 ledger))
        (equal (fn-sni-role-entry :reader (fn-prl-nth 6 (fn-snir-initial next maintenance)))
               (list :reader :held token)))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-sni-role-claim-preserves-charge-and-source
                  (role :reader) (token (list :initial-reader maintenance source root-ticket (mv-nth 2 (fn-hsr-source-begin (fn-hrs-h-rec (fn-prl-nth 5 (fn-prl-nth 3 (fn-snir-initial ledger maintenance)))) page-source root-ticket maintenance)))))
                (:instance fn-snir-source-begin-car-never-reader-word (root (fn-hrs-h-rec (fn-prl-nth 5 (fn-prl-nth 3 (fn-snir-initial ledger maintenance)))))))
          :in-theory
          (e/d (fn-snir-begin)
               (fn-snir-sourcep fn-hsr-source-begin fn-hrs-h-rec fn-snir-initial
                fn-sni-role-claim fn-sni-livep fn-prl-nth fn-sni-role-entry
                fn-snir-source-begin-car-never-reader-word)))))

(in-theory (disable fn-snir-initial fn-snir-sourcep fn-snir-begin))
