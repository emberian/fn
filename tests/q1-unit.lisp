; Q1 controls: the assembled catalogue is E1's 39 labels and the scribe's :refused plus the listener's
; :admitting phase (R7's split, agreed with layer D) plus B's 15 commit labels
; (a pinned regression; conn's :query and the cursor's eight phases since D6
; 1/n; E's fn2-ctl (nine phases, four observes) and fn2-cns (ten phases) since
; edb0f5dd8/9860d85a5, re-pinned 2026-11-05 with the 23 added rows named in the commit;
; the upload's :store phases and observes and the cursor's :fetch (lane article-octets, 10 rows),
; served authority's fn2-auth (twelve phases, lane authority step 2's kind, 12 rows, 2026-11-06),
; image boot (17 phases and 3 observes, lane disk-boot),
; control, DSL-METATHEORY 5.8), every label is bound, the composition row is
; the unchanged fn2-turn-refinement, and a declared role that does not occur in
; the generated statement is refused (E2's role-divergence control).
(in-package "ACL2")
(include-book "../books/q1")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn2-q1-pinned-catalogue*
  '((:run fn2-listener :accepting) (:run fn2-listener :admitting) (:run fn2-listener :closing)
    (:observe fn2-listener :accept-result) (:observe fn2-listener :close-result)
    (:run fn2-echo :free) (:run fn2-echo :command) (:run fn2-echo :reply)
    (:run fn2-echo :closing) (:run fn2-echo :draining) (:run fn2-echo :retired)
    (:observe fn2-echo :receive-result) (:observe fn2-echo :send-result)
    (:observe fn2-echo :borrow-released) (:observe fn2-echo :close-result)
    (:run fn2-scribe :free) (:run fn2-scribe :reserve) (:run fn2-scribe :fill)
    (:run fn2-scribe :patch) (:run fn2-scribe :write) (:run fn2-scribe :write-result)
    (:run fn2-scribe :fence) (:run fn2-scribe :fence-result) (:run fn2-scribe :reset)
    (:run fn2-scribe :read) (:run fn2-scribe :read-result) (:run fn2-scribe :verify)
    (:run fn2-scribe :next) (:run fn2-scribe :stopped) (:run fn2-scribe :refused)
    (:observe fn2-scribe :write-result) (:observe fn2-scribe :fence-result)
    (:observe fn2-scribe :read-result) (:run fn2-commit :free) (:run fn2-commit :collect)
    (:run fn2-commit :seal) (:run fn2-commit :dependencies) (:run fn2-commit :log-write)
    (:run fn2-commit :fence) (:run fn2-commit :durable) (:run fn2-commit :install)
    (:run fn2-commit :publish) (:run fn2-commit :notify) (:run fn2-commit :draining)
    (:run fn2-commit :uncertain) (:run fn2-commit :dropping) (:observe fn2-commit :write-result)
    (:observe fn2-commit :fence-result) (:run fn2-recovery-machine :free)
    (:run fn2-recovery-machine :read) (:run fn2-recovery-machine :read-result)
    (:run fn2-recovery-machine :verify) (:run fn2-recovery-machine :search)
    (:run fn2-recovery-machine :install) (:run fn2-recovery-machine :done)
    (:observe fn2-recovery-machine :read-result) (:run fn2-sealer :sealing)
    (:run fn2-sealer :stopped) (:run fn2-conn :free) (:run fn2-conn :greeting)
    (:run fn2-conn :command) (:run fn2-conn :article-input) (:run fn2-conn :reply)
    (:run fn2-conn :upgrading) (:run fn2-conn :closing) (:run fn2-conn :draining)
    (:run fn2-conn :retired) (:run fn2-conn :query) (:observe fn2-conn :receive-result)
    (:observe fn2-conn :send-result) (:observe fn2-conn :borrow-released)
    (:observe fn2-conn :close-result) (:run fn2-upload :free) (:run fn2-upload :head)
    (:run fn2-upload :identity) (:run fn2-upload :receiving) (:run fn2-upload :validating)
    (:run fn2-upload :discard) (:run fn2-upload :store) (:run fn2-upload :store-write)
    (:run fn2-upload :store-wrote) (:run fn2-upload :store-fence)
    (:run fn2-upload :store-fenced) (:run fn2-upload :sealed) (:run fn2-upload :aborting)
    (:run fn2-upload :draining) (:run fn2-upload :retired) (:observe fn2-upload :write-result)
    (:observe fn2-upload :fence-result) (:observe fn2-upload :borrow-released)
    (:run fn2-txn :free) (:run fn2-txn :admit) (:run fn2-txn :reserve) (:run fn2-txn :lookup)
    (:run fn2-txn :prepare) (:run fn2-txn :ready) (:run fn2-txn :batched)
    (:run fn2-txn :accepted) (:run fn2-txn :refused) (:run fn2-txn :uncertain)
    (:run fn2-txn :releasing) (:run fn2-txn :draining) (:run fn2-txn :retired)
    (:run fn2-cursor :free) (:run fn2-cursor :select) (:run fn2-cursor :seek)
    (:run fn2-cursor :render) (:run fn2-cursor :send) (:run fn2-cursor :fetch)
    (:run fn2-cursor :finish) (:run fn2-cursor :draining) (:run fn2-cursor :retired)
    (:observe fn2-cursor :read-result) (:run fn2-ctl :free) (:run fn2-ctl :greeting)
    (:run fn2-ctl :frame) (:run fn2-ctl :dispatch) (:run fn2-ctl :waiting) (:run fn2-ctl :reply)
    (:run fn2-ctl :closing) (:run fn2-ctl :draining) (:run fn2-ctl :retired)
    (:observe fn2-ctl :receive-result) (:observe fn2-ctl :send-result)
    (:observe fn2-ctl :borrow-released) (:observe fn2-ctl :close-result) (:run fn2-cns :free)
    (:run fn2-cns :decode) (:run fn2-cns :check) (:run fn2-cns :lookup) (:run fn2-cns :read)
    (:run fn2-cns :page) (:run fn2-cns :fetch) (:run fn2-cns :park) (:run fn2-cns :commit)
    (:run fn2-cns :committed) (:run fn2-cns :append) (:run fn2-cns :draining) (:run fn2-cns :retired)
    (:observe fn2-cns :read-result) (:run fn2-auth :free) (:run fn2-auth :decode)
    (:run fn2-auth :lookup) (:run fn2-auth :allocate) (:run fn2-auth :bhead)
    (:run fn2-auth :outcome) (:run fn2-auth :head) (:run fn2-auth :get) (:run fn2-auth :ready)
    (:run fn2-auth :batched) (:run fn2-auth :draining) (:run fn2-auth :retired)
    (:run fn2-boot :free) (:run fn2-boot :prepare) (:run fn2-boot :write)
    (:run fn2-boot :write-result) (:run fn2-boot :read) (:run fn2-boot :read-result)
    (:run fn2-boot :verify) (:run fn2-boot :advance) (:run fn2-boot :anchor)
    (:run fn2-boot :recover) (:run fn2-boot :recover-wait) (:run fn2-boot :epoch)
    (:run fn2-boot :epoch-fence) (:run fn2-boot :epoch-result) (:run fn2-boot :release)
    (:run fn2-boot :ready) (:run fn2-boot :failed) (:observe fn2-boot :read-result)
    (:observe fn2-boot :write-result) (:observe fn2-boot :fence-result)
    (:router :fallback) (:executor :clock) (:executor :signal) (:executor :service 0)
    (:executor :service 1) (:executor :service 2) (:executor :service 3)
    (:executor :empty-principal)))
(assert-event (equal (fn2-case-catalogue (w state)) *fn2-q1-pinned-catalogue*))
(assert-event (equal (len *fn2-q1-pinned-catalogue*) 179))
(assert-event
 (equal (fn2-square-coverage 'fn2-q1 (w state))
        '(:required 179 :bound 179 :unmatched nil
          :unresolved-depends (fn2-q1-entry fn2-q1-exit fn2-q1-partition))))
(assert-event
 (equal (fn2-decl-get :owner (fn2-decl-row '(:square fn2-turn-refinement) (w state)))
        '(:correspondence fn2-q1)))
(value-triple (cw "Q1 CATALOGUE: 179 labels = E1's 39 + listener :admitting + 15 B commit + 8 B recovery + 2 C fn2-sealer + 13 D fn2-conn + 18 D fn2-upload + 13 D fn2-txn + 10 D fn2-cursor + 13 E fn2-ctl + 11 E fn2-cns + 12 E fn2-auth + 20 boot (171 machine, 1 router, 7 executor); 179 bound, 0 unmatched PASS~%"))

; E2's divergence control: the generated statement kept, the relation role
; declared as the nested pure relation instead of the full invariant.
(make-event
 (value
  `(must-fail
    (defsquare fn2-q1-role-divergence
      :template :q1-loop-iteration :cases-from (list (car *fn2-q1-pinned-catalogue*))
      :bindings
      (list (cons (car *fn2-q1-pinned-catalogue*)
                  (fn2-decl-set :id 'fn2-q1-role-divergence-row
                    (cdar (fn2-q1-bind-cases (list (car *fn2-q1-pinned-catalogue*)) 0
                                            *fn2-q1-contract* *fn2-q1-sides* (w state))))))
      :contract ,(fn2-decl-set :relation 'fn2-q1-loop-relatedp *fn2-q1-contract*)
      :sides ,*fn2-q1-sides*)
    :with-output-off nil)))
(assert-event (and (not (fn2-decl-row '(:square fn2-q1-role-divergence-row) (w state)))
                   (not (fn2-decl-row '(:correspondence fn2-q1-role-divergence) (w state)))))
(value-triple (cw "Q1 ROLES: relation-role divergence refused PASS~%"))
