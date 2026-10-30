(in-package "ACL2")
(include-book "../books/assembly")
(include-book "std/testing/must-fail" :dir :system)

; Every declared continuation resolved at :callbacks, with authoritative formals.
(fn2-resolve :callbacks)
(assert-event
 (let* ((row (fn2-operation-row 'fn2-listener-admit (w state)))
        (owner (fn2-decl-row '(:machine fn2-listener) (w state))))
   (and (assoc-eq 'fn2-listener-admit (fn2-decl-get :callbacks owner))
        (equal (fn2-decl-get :calling-convention row)
               (getpropc 'fn2-listener-admit 'formals nil (w state)))
        ; only the fields its body reads, never the whole row
        (let ((reads (fn2-decl-get :row-bindings row))
              (all (fn2-machine-row-vars (fn2-machine-property 'fn2-listener :columns (w state)))))
          (and (consp reads) (subsetp-eq reads all) (< (len reads) (len all))))
        (eq (fn2-decl-get :section row) :callbacks))))
(assert-event
 (and (equal (fn2-decl-get :owner (fn2-operation-row 'fn2-issue-send (w state)))
             '(:operation-set fn2-core-issue))
      (equal (fn2-decl-get :refusal (fn2-operation-row 'fn2-issue-send (w state)))
             '(:square fn2-issue-send-refusal))
      (equal (fn2-decl-get :owner (fn2-operation-row 'fn2-harvest-one (w state)))
             '(:operation-set fn2-core-harvest))
      (fn2-operation-row 'fn2-listener-return-credit (w state))
      (fn2-operation-row 'fn2-machine-park (w state))
      (fn2-operation-row 'fn2-machine-grant-op (w state))
      (fn2-operation-row 'fn2-machine-park-admission (w state))
      (fn2-operation-row 'fn2-machine-grant-admission (w state))))

; A real forwarding callback succeeds, the old positional spelling is refused.
; These DM0b controls exercise the emitter's snapshot refresh, which reads a
; row after writing it: the restricted arm language refuses that (a stale
; read), so they are declared :language :unchecked, the declared escape.
(defmachine-callback fn2-dm-forward fn2-listener (id budget) 4
  :contract (:cost (:steps *fn2-work-transition*) :writes (event-ready) :next (:accepting :closing)
             :tables (fn2-core-machines fn2-core-pool fn2-echo-table)
             :uses (fn2-listener-admit) :language :unchecked)
  (fn2-call fn2-listener-admit id budget))
(must-fail
 (make-event
  (value (fn2-machine-callback-event 'fn2-dm-positional 'fn2-listener '(id budget) 4 nil
           (list (cons 'fn2-listener-admit
                       (fn2-decl-get :calling-convention
                         (fn2-operation-row 'fn2-listener-admit (w state))))) (w state))))
 :expected :soft)
(assert-event
 (not (fn2-callback-forwarding
        '(quote (fn2-listener-admit id budget row-phase)) '(row-phase) (w state))))
(assert-event
 (not (fn2-callback-forwarding
        '(let ((row-phase 0)) (fn2-listener-admit row-phase)) '(row-phase) (w state))))

(must-fail (defmachine-callback fn2-dm-missing fn2-listener (id budget) 4
             (fn2-call fn2-dm-absent id budget)) :expected :soft)
(must-fail (defmachine-callback fn2-dm-arity fn2-listener (id budget) 4
             (fn2-call fn2-listener-admit id)) :expected :soft)
(must-fail (defmachine-callback fn2-dm-binder fn2-listener (id budget) 1
             (b* (((when t) (mv id fn2-core))) (mv id fn2-core))) :expected :soft)
(defmachine-callback fn2-dm-bstar fn2-listener (id budget) 1
  :contract (:cost (:steps *fn2-work-transition*) :writes (event-ready) :next (:accepting :closing)
             :tables (fn2-core-machines fn2-core-pool fn2-echo-table)
             :uses (fn2-listener-admit) :language :unchecked)
  (b* ((fn2-core (fn2-listener-put-core id (event-ready 1))))
    (mv row-event-ready fn2-core)))

; Read the result of a successful write AND a refused write, not proposed data.
(defmachine-callback fn2-dm-refresh fn2-listener (id budget) 1
  :contract (:cost (:steps *fn2-work-transition*) :writes (event-ready) :next (:accepting :closing)
             :tables (fn2-core-machines fn2-core-pool fn2-echo-table)
             :uses (fn2-listener-admit) :language :unchecked)
  (let* ((fn2-core (fn2-listener-put-core id (event-ready 1)))
         (fresh row-event-ready)
         (fn2-core (fn2-listener-put-core id (event-ready 256))))
    (mv (and (equal fresh 1) (equal row-event-ready 1)) fn2-core)))
(defun fn2-dm-refresh-control ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
   (mv-let (ok fn2-core)
     (let ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core)))
       ; its only read field is event-ready: that is its whole row argument
       (fn2-dm-refresh 0 1 (fn2-listener-row-event-ready 0 fn2-core) fn2-core))
     ok)))
(assert-event (fn2-dm-refresh-control))

; Machine/child inputs are closed; evidence is a separate, still-open input.
(must-fail
 (defmachine fn2-dm-late :states (:idle) :fields nil 
   :budget (:bytes 0 :steps 1 :descriptors 0) :continuations ((:idle fn2-dm-idle :cost (:steps 0) :writes () :next (:idle) :uses ())))
 :expected :soft)
(defcolumns fn2-dm-child ((value :u8)))
(must-fail (defcorechild fn2-dm-child-table fn2-dm-child :init fn2-dm-child
             :profilep t :why "Too late after core.") :expected :soft)
(defun fn2-dm-tooth () t)
(defthm-owed fn2-dm-late-evidence (x) (equal x x) :teeth (fn2-dm-tooth))
(fn2-resolve :coverage)
(fn2-seal :evidence :coverage :square)
(must-fail (defthm-owed fn2-dm-too-late (x) (equal x x) :teeth (fn2-dm-tooth))
           :expected :soft)
(value-triple (cw "DM0b CALLBACKS: forwarding, fresh/refused writes, owner maps, per-input seals PASS~%"))
