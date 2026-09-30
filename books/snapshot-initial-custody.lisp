; INITIAL issuer core. Its host boundary must read the source and runtime
; records from their actual installed owners. No native supplied-demand ABI.
(in-package "ACL2")
(include-book "snapshot-initial-request")
(include-book "snapshot-source-cursor")

(defun fn-sni-sourcep (source descriptor)
  (declare (xargs :guard t))
  (and (fn-sni-widthp source 4)
       (equal (fn-prl-nth 0 source) :recovery-source)
       (natp (fn-prl-nth 1 source))
       (natp (fn-prl-nth 2 source))
       (natp (fn-prl-nth 3 source))
       (fn-sni-widthp descriptor 9)
       (equal (fn-prl-nth 0 descriptor) :recovery-census)
       (equal (fn-prl-nth 1 descriptor) source)
       (equal (fn-prl-nth 2 descriptor) (fn-prl-nth 2 source))
       (natp (fn-prl-nth 3 descriptor))
       (natp (fn-prl-nth 6 descriptor))
       (natp (fn-prl-nth 7 descriptor))))

(defun fn-sni-reserved-roles ()
  (declare (xargs :guard t))
  '((:source-root :reserved nil) (:payload-view :reserved nil)
    (:workspace :reserved nil) (:job :reserved nil)
    (:allocation-turn :reserved nil) (:reader :reserved nil)
    (:private-backing :reserved nil)))

(defun fn-sni-keep-initial (ledger maintenance receipt)
  ; Called only on the exact newly prepended successful admission row.
  (declare (xargs :guard t))
  (let* ((bindings (fn-prl-nth 3 ledger))
         (entry (if (consp bindings) (car bindings) nil))
         (row (if (consp entry) (cdr entry) nil)))
    (fn-prl-build
     (fn-prl-nth 0 ledger) (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
     (cons (cons maintenance (fn-pmn-row (fn-prl-nth 0 row) nil receipt))
           (if (consp bindings) (cdr bindings) nil))
     (fn-prl-nth 4 ledger))))

(defun fn-sni-issue (ledger source descriptor family table)
  (declare (xargs :guard t))
  (let ((context (fn-osrc-source-context
                  (fn-prl-nth 5 descriptor) (fn-prl-nth 6 descriptor)
                  (fn-prl-nth 7 descriptor) :ready)))
    (if (not (and (fn-sni-sourcep source descriptor)
                  (equal (fn-prl-nth 0 context) :ready)))
        (mv '(:unavailable :initial-source) ledger)
      (mv-let (word demand) (fn-sni-initial-demand family table)
        (if (not (equal word :available))
            (mv '(:unavailable :initial-runtime-family) ledger)
          (mv-let (word maintenance next)
            (fn-pmn-admit ledger (fn-prl-nth 1 context)
                          (fn-prl-nth 4 context) demand)
            (if (not (equal word :admitted)) (mv (list :unavailable word) ledger)
              (let ((receipt (list :initial source descriptor context family table
                                   (fn-sni-reserved-roles))))
                (mv (list :admitted source maintenance maintenance
                          (fn-sni-reserved-roles))
                    (fn-sni-keep-initial next maintenance receipt))))))))))

(defun fn-sni-livep (ledger source maintenance)
  (declare (xargs :guard t))
  (let* ((entry (fn-prl-binding maintenance (fn-prl-nth 3 ledger)))
         (row (if (consp entry) (cdr entry) nil))
         (initial (fn-prl-nth 3 row))
         (context (fn-prl-nth 3 initial)))
    (and (equal (fn-prl-nth 1 row) :maintenance)
         (fn-sni-widthp initial 7)
         (equal (fn-prl-nth 0 initial) :initial)
         (equal (fn-prl-nth 1 initial) source)
         (equal (fn-prl-nth 0 maintenance) :maintenance)
         (equal (fn-prl-nth 2 maintenance) (fn-prl-nth 1 context))
         (equal (fn-prl-nth 3 maintenance) (fn-prl-nth 4 context)))))

; Role acquisition belongs inside its actual core acquire boundary, before
; the holder escapes. This helper alone proves no native holder association.
(defun fn-sni-claim-role-list (roles role token)
  (declare (xargs :guard t))
  (if (consp roles)
      (if (equal role (fn-prl-nth 0 (car roles)))
          (if (equal (fn-prl-nth 1 (car roles)) :reserved)
              (mv :claimed (cons (list role :held token) (cdr roles)))
            (mv :unavailable roles))
        (mv-let (word rest) (fn-sni-claim-role-list (cdr roles) role token)
          (if (equal word :claimed) (mv word (cons (car roles) rest))
            (mv word roles))))
    (mv :unavailable roles)))

(defun fn-sni-role-claim (ledger maintenance source role token)
  (declare (xargs :guard t))
  (if (not (fn-sni-livep ledger source maintenance)) (mv :stale ledger)
    (let* ((bindings (fn-prl-nth 3 ledger))
           (entry (fn-prl-binding maintenance bindings))
           (row (if (consp entry) (cdr entry) nil))
           (initial (fn-prl-nth 3 row)))
      (mv-let (word roles)
        (fn-sni-claim-role-list (fn-prl-nth 6 initial) role token)
        (if (not (equal word :claimed)) (mv word ledger)
          (mv :claimed
              (fn-prl-build
               (fn-prl-nth 0 ledger) (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
               (cons (cons maintenance
                           (fn-pmn-row (fn-prl-nth 0 row) (fn-prl-nth 2 row)
                                       (list :initial (fn-prl-nth 1 initial)
                                             (fn-prl-nth 2 initial)
                                             (fn-prl-nth 3 initial)
                                             (fn-prl-nth 4 initial)
                                             (fn-prl-nth 5 initial) roles)))
                     (fn-prl-remove maintenance bindings))
               (fn-prl-nth 4 ledger))))))))

(defun fn-sni-role-dependents (role)
  (declare (xargs :guard t))
  (cond ((equal role :source-root)
         '(:payload-view :workspace :job :reader :private-backing :allocation-turn))
        ((equal role :payload-view)
         '(:workspace :job :reader :private-backing :allocation-turn))
        ((equal role :workspace) '(:job :allocation-turn))
        ((equal role :reader) '(:job :allocation-turn))
        ((equal role :private-backing) '(:job :allocation-turn))
        (t nil)))

(defun fn-sni-roles-returnedp (dependents roles)
  (declare (xargs :guard t))
  (if (consp dependents)
      (let ((entry (fn-sni-role-entry (car dependents) roles)))
        (and (member-eq (fn-prl-nth 1 entry) '(:reserved :returned))
             (fn-sni-roles-returnedp (cdr dependents) roles)))
    (null dependents)))

(defun fn-sni-role-releasablep (ledger maintenance source role token)
  (declare (xargs :guard t))
  (let* ((row (cdr (fn-prl-binding maintenance (fn-prl-nth 3 ledger))))
         (roles (fn-prl-nth 6 (fn-prl-nth 3 row)))
         (entry (fn-sni-role-entry role roles)))
    (and (fn-sni-livep ledger source maintenance)
         (equal (fn-prl-nth 1 entry) :held)
         (equal (fn-prl-nth 2 entry) token)
         (fn-sni-roles-returnedp (fn-sni-role-dependents role) roles))))

(defun fn-sni-return-role-list (roles role token)
  (declare (xargs :guard t))
  (if (consp roles)
      (if (equal role (fn-prl-nth 0 (car roles)))
          (cons (list role :returned token) (cdr roles))
        (cons (car roles) (fn-sni-return-role-list (cdr roles) role token)))
    roles))

; Internal epilogue used only in composition with the actual role-specific
; core :released result. This is not a public joined/alias observation API.
; It deliberately retains INITIAL and all charges; it never resets A.
(defun fn-sni-role-return (ledger maintenance source role token)
  (declare (xargs :guard t))
  (if (not (fn-sni-role-releasablep ledger maintenance source role token))
      (mv :initial-custody-retained ledger)
    (let* ((bindings (fn-prl-nth 3 ledger))
           (entry (fn-prl-binding maintenance bindings))
           (row (if (consp entry) (cdr entry) nil))
           (initial (fn-prl-nth 3 row))
           (roles (fn-sni-return-role-list (fn-prl-nth 6 initial) role token)))
      (mv :returned
          (fn-prl-build
           (fn-prl-nth 0 ledger) (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
           (cons (cons maintenance
                       (fn-pmn-row (fn-prl-nth 0 row) (fn-prl-nth 2 row)
                                   (list :initial (fn-prl-nth 1 initial)
                                         (fn-prl-nth 2 initial)
                                         (fn-prl-nth 3 initial)
                                         (fn-prl-nth 4 initial)
                                         (fn-prl-nth 5 initial) roles)))
                 (fn-prl-remove maintenance bindings))
           (fn-prl-nth 4 ledger))))))

(defthm fn-sni-issued-source-and-retained-custody
  (implies (equal (fn-prl-nth 0
                  (mv-nth 0 (fn-sni-issue ledger source descriptor family table)))
                  :admitted)
           (let* ((answer (mv-nth 0 (fn-sni-issue ledger source descriptor family table)))
                  (maintenance (fn-prl-nth 2 answer))
                  (next (mv-nth 1 (fn-sni-issue ledger source descriptor family table)))
                  (context (fn-osrc-source-context
                            (fn-prl-nth 5 descriptor) (fn-prl-nth 6 descriptor)
                            (fn-prl-nth 7 descriptor) :ready)))
             (and (fn-sni-sourcep source descriptor)
                  (equal (fn-prl-nth 1 answer) source)
                  (equal maintenance (fn-prl-nth 3 answer))
                  (equal maintenance
                         (list :maintenance (fn-prl-nth 2 ledger)
                               (fn-prl-nth 1 context) (fn-prl-nth 4 context)))
                  (equal (fn-prl-nth 4 answer) (fn-sni-reserved-roles))
                  (equal (fn-prl-nth 3
                          (cdr (fn-prl-binding maintenance (fn-prl-nth 3 next))))
                         (list :initial source descriptor context family table
                               (fn-sni-reserved-roles)))
                  (fn-sni-livep next source maintenance))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-sni-issue fn-sni-keep-initial fn-sni-livep fn-pmn-admit
                 fn-pmn-row fn-prl-binding fn-prl-build fn-prl-nth
                 fn-sni-widthp)
                (fn-prs-issue fn-sni-initial-demand fn-osrc-source-context
                 fn-sni-sourcep fn-sni-reserved-roles)))))

(defthm fn-sni-role-claim-preserves-charge-and-source
  (implies (equal (mv-nth 0
                  (fn-sni-role-claim ledger maintenance source role token)) :claimed)
           (let ((next (mv-nth 1
                        (fn-sni-role-claim ledger maintenance source role token))))
             (and (fn-sni-livep next source maintenance)
                  (equal (fn-prl-nth 0 next) (fn-prl-nth 0 ledger))
                  (equal (fn-prl-nth 1 next) (fn-prl-nth 1 ledger))
                  (equal (fn-prl-nth 2 next) (fn-prl-nth 2 ledger))
                  (equal (fn-prl-nth 4 next) (fn-prl-nth 4 ledger)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-sni-role-claim fn-sni-livep fn-pmn-row fn-prl-binding
                 fn-prl-build fn-prl-nth fn-sni-widthp)
                (fn-sni-claim-role-list)))))

(in-theory (disable fn-sni-sourcep fn-sni-reserved-roles fn-sni-keep-initial
                    fn-sni-issue fn-sni-livep fn-sni-claim-role-list
                    fn-sni-role-claim fn-sni-role-dependents fn-sni-roles-returnedp
                    fn-sni-role-releasablep fn-sni-return-role-list fn-sni-role-return))
