; Request/control incarnation binding at the actual consumer authorization gate.
; This is a structural-state guarantee, not the complete grant-publication theorem.
(in-package "ACL2")
(include-book "assembly-callbacks-e-cns")

(defun fn2-cns-binding-currentp (cns gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (eq (fn2-cns-snapshot-read-code cns fn2-core) :ok)
       (equal (fn2-machine-generation cns fn2-core) gen)
       (let ((ctl (fn2-cns-row-ctl cns fn2-core)))
         (and (eq (fn2-ctl-snapshot-read-code ctl fn2-core) :ok)
              (equal (fn2-machine-generation ctl fn2-core)
                     (fn2-cns-row-ctl-gen cns fn2-core))))))

(defthm fn2-cns-principal-current-binding
  (implies (fn2-cns-binding-currentp cns gen fn2-core)
           (equal (fn2-cns-principal cns gen fn2-core)
                  (mv :ok (nfix (fn2-ctl-row-principal
                                  (fn2-cns-row-ctl cns fn2-core) fn2-core)))))
  :hints (("Goal" :in-theory (enable fn2-cns-binding-currentp fn2-cns-principal))))

(defthm fn2-cns-principal-stale-binding
  (implies (not (fn2-cns-binding-currentp cns gen fn2-core))
           (equal (fn2-cns-principal cns gen fn2-core) (mv :state 0)))
  :hints (("Goal" :in-theory (enable fn2-cns-binding-currentp fn2-cns-principal))))

; The full returned core is unchanged: refusal precedes admin bypass, release
; of an old read, and all grant lookups. No assumption about XSTEP is needed.
(defthm fn2-cns-authority-stale-binding-refusal
  (implies (and (fn2-auth-served fn2-core)
                (not (fn2-cns-binding-currentp cns gen fn2-core)))
           (equal (fn2-cns-authority-allows cns gen right scope target
                                          xstep head grant budget fn2-core)
                  (mv :state 0 0 0 fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-cns-authority-allows)
                                  (fn2-cns-binding-currentp fn2-cns-principal)))))

(defthm fn2-cns-authority-current-admin
  (implies (and (fn2-auth-served fn2-core)
                (fn2-cns-binding-currentp cns gen fn2-core)
                (fn2-cns-admin-p cns fn2-core))
           (equal (fn2-cns-authority-allows cns gen right scope target
                                          xstep head grant budget fn2-core)
                  (mv :ok 0 0 0 fn2-core)))
  :hints (("Goal" :in-theory (e/d (fn2-cns-authority-allows)
                                  (fn2-cns-binding-currentp fn2-cns-principal)))))
(in-theory (disable fn2-cns-binding-currentp))
