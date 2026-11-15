; Physical startup/one-POST envelope, independent of runtime admission policy.
; Existing query references pin their physical slots; they are not extra leases.
(in-package "ACL2")
(include-book "pool")
(include-book "upload-page-geometry")
(include-book "identity-workspace-geometry")
(include-book "successor-schema-geometry")
(include-book "run-geometry")
(include-book "identity")
(include-book "ordered")
(include-book "folds")
(fn2-book-layer :c)

; These are the actual typed writer families called by the POST producer.
; IDs come from the existing schema declarations; no independent numeric cap.
(defconst *fn2-checkpoint-post-schema-families*
 '(fn2-identity-history fn2-identity-evidence fn2-identity-candidates
   fn2-identity-summary fn2-identity-article fn2-article fn2-outcome
   fn2-addr fn2-group-counts fn2-overview))
(defun fn2-checkpoint-service-schema-ids (families world)
 (declare (xargs :verify-guards nil :measure (len families)))
 (if (atom families) nil
  (let* ((row (fn2-decl-row (list :schema (car families)) world))
         (id (fn2-decl-get :id row)))
   (if (not (and row (natp id))) nil
    (cons id (fn2-checkpoint-service-schema-ids (cdr families) world))))))
(make-event
 (let ((ids (fn2-checkpoint-service-schema-ids *fn2-checkpoint-post-schema-families* (w state))))
  (if (not (and (= (len ids) (len *fn2-checkpoint-post-schema-families*))
                (equal ids (remove-duplicates-equal ids))))
      (er soft 'fn2-checkpoint-service-schema-ids "POST writer schema footprint is missing or aliases a schema.")
    (value `(defconst *fn2-checkpoint-post-schema-ids* ',ids)))))

; Boot pack/rx overlap recovery window/workspace. The cold root page is
; generic, not a loan from the separately protected checkpoint working group.
(defconst *fn2-checkpoint-startup-sector-windows*
 '(boot-pack boot-rx recovery-window recovery-workspace))
(defconst *fn2-checkpoint-cold-root-windows* '(checkpoint-root))

(defun fn2-checkpoint-name-arena-count (profile)
 (declare (xargs :guard t))
 (+ (if (consp (fn2-profile-get :groups profile)) 1 0)
    (if (posp (nfix (fn2-profile-get :authority profile))) 1 0)))
(defun fn2-checkpoint-service-class-demand (class profile sector-class scratch-class arena-class page-class root-class)
 (declare (xargs :guard t))
 (let* ((names (fn2-checkpoint-name-arena-count profile))
        (scratch (if (equal class scratch-class) 1 0))
        (arenas (if (equal class arena-class) 1 0))
        (root (if (equal class root-class) (len *fn2-checkpoint-cold-root-windows*) 0))
        (startup (* (if (equal class sector-class) 1 0)
                    (len *fn2-checkpoint-startup-sector-windows*)))
        (fresh (+ startup (if (posp names) scratch 0) (* names arenas)))
        (cold (+ startup root))
        (post (+ scratch (* (len *fn2-checkpoint-post-schema-ids*) arenas)
                 (if (equal class *fn2-upload-chunk-class*) 2 0)
                 (if (equal class page-class) 1 0)))
        ; The accepted epoch-result root release precedes recovery finalization
        ; and every listener/READY transition. The root overlaps startup only.
        (fresh-post (+ post (* names arenas)))
        (cold-post post))
  (max (max fresh cold) (max fresh-post cold-post))))
(defun fn2-checkpoint-service-vector-loop (class profile sector-class scratch-class arena-class page-class root-class fn2-pool)
 (declare (xargs :stobjs fn2-pool
  :guard (and (fn2-pool-wfp fn2-pool) (natp class))
  :measure (nfix (- (nfix (fn2-pool-nclasses fn2-pool)) (nfix class)))))
 (if (not (and (natp class) (< class (nfix (fn2-pool-nclasses fn2-pool))))) nil
  (cons (fn2-checkpoint-service-class-demand class profile sector-class scratch-class arena-class page-class root-class)
        (fn2-checkpoint-service-vector-loop (+ class 1) profile sector-class scratch-class arena-class page-class root-class fn2-pool))))
(defun fn2-checkpoint-service-demand-vector (profile fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
 (let* ((arena (fn2-idc-profile-arena profile))
        (chunk *fn2-upload-chunk-class*))
  (if (not (and (fn2-upload-article-profilep profile)
                (posp arena) (unsigned-byte-p 32 arena)
                (natp chunk) (< chunk (fn2-pool-nclasses fn2-pool))))
      (mv :profile nil)
   (let* ((capacity (fn2-pool-class-sizesi chunk fn2-pool))
          (bound (fn2-upload-input-bound (fn2-upload-profile-article-max profile) capacity capacity))
          (sector-class (fn2-pool-class-for *fn2-format-sector-bytes* fn2-pool))
          (scratch-class (fn2-pool-class-for *fn2-idc-scratch-bytes* fn2-pool))
          (arena-class (fn2-pool-class-for arena fn2-pool))
          (page-class (fn2-pool-class-for (fn2-upload-page-bytes (+ bound *fn2-upload-mid-line-max*)) fn2-pool))
          (root-class (fn2-pool-class-for *fn2-format-page-size* fn2-pool)))
    (if (not (and (posp capacity)
                  (natp sector-class) (< sector-class (fn2-pool-nclasses fn2-pool))
                  (natp scratch-class) (< scratch-class (fn2-pool-nclasses fn2-pool))
                  (natp arena-class) (< arena-class (fn2-pool-nclasses fn2-pool))
                  (natp page-class) (< page-class (fn2-pool-nclasses fn2-pool))
                  (natp root-class) (< root-class (fn2-pool-nclasses fn2-pool))))
        (mv :capacity nil)
      (mv :ok (fn2-checkpoint-service-vector-loop 0 profile sector-class scratch-class arena-class page-class root-class fn2-pool)))))))
