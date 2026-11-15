; Concrete coverage inventory for the CLOSED served world. This is proof
; metadata, not a runtime scan and not a statement that the obligations
; below have admitted. All proposed obligation forms remain UNRUN.
(in-package "ACL2")
(include-book "query-reference-accounting")
(include-book "core-walk")
(include-book "assembly-callbacks")
(include-book "assembly-callbacks-d-conn")
(include-book "assembly-callbacks-d-upload")
(include-book "assembly-callbacks-d-txn")
(include-book "assembly-callbacks-d-cursor")
(include-book "assembly-callbacks-e-auth")
(include-book "host-ops")
(include-book "executor-wake")
(fn2-book-layer :c)

; The categories state the actual boundary each proof must cover. Raw
; setters, loops and counted half-steps are never assumed to preserve the
; global relation on their own; all their actual core callers are inventoried.
(defconst *fn2-qr-proof-boundaries*
 '((:pool-guarded :subject fn2-qr-ordinary-pool-operation-frame
     :operations (fn2-pool-reserve fn2-pool-release fn2-pool-write fn2-pool-reset
                  fn2-pool-lease-in fn2-pool-adapter-write fn2-pool-complete-in
                  fn2-pool-lease-out fn2-pool-release-out fn2-pool-hand fn2-pool-accept-hand))
   (:range-guarded :operations (fn2-pool-copy-range fn2-pool-drop-prefix fn2-pool-truncate fn2-pool-accept-own))
   (:paired-counted :operations (fn2-pool-query-acquire fn2-pool-query-release)
     :callers (fn2-id-decide-start fn2-id-query-release))
   (:query-lifecycle :operations (fn2-id-decide-start fn2-id-decide-step fn2-id-query-release
                                  fn2-succ-release fn2-succ-replay-sweep))
   (:metadata-only :operations (fn2-peer-import-start-key fn2-query-ref-flush)
     :fields (qnamespace qprofile qalgorithm qwake query-incarnation sfound selected candidates gaps
              cfound h evidence qualified local))
   (:guarded-internal-only :operations (fn2-pool-copy-up fn2-pool-copy-down
                                        update-fn2-pool-datai))
   (:bootstrap-separate :operations (fn2-pool-columns-init fn2-pool-init fn2-pool-carve-slots
                                    fn2-pool-carve-classes fn2-id-decides-init fn2-id-decides-init-for
                                    init-fn2-core-pool init-fn2-core-id-decides fn2-core-init))))

; Discover actual writers from stobjs-out, as the established borrow-face
; walk does. This includes generated setters/resizes and catches additions.
(defun fn2-qr-world-writers (stobj wrld acc)
 (declare (xargs :verify-guards nil))
 (if (atom wrld) acc
  (let ((trip (car wrld)))
   (fn2-qr-world-writers stobj (cdr wrld)
    (if (and (eq (cadr trip) 'stobjs-out) (true-listp (cddr trip))
             (member-eq stobj (cddr trip)) (not (member-eq (car trip) acc)))
        (cons (car trip) acc) acc)))))
(defun fn2-qr-core-body-entries (wrld wrld0 acc)
 (declare (xargs :verify-guards nil))
 (if (atom wrld) acc
  (let* ((trip (car wrld)) (f (car trip)) (outs (getpropc f 'stobjs-out nil wrld0)))
   (fn2-qr-core-body-entries (cdr wrld) wrld0
    (if (and (eq (cadr trip) 'unnormalized-body) (not (assoc-eq f acc))
             (true-listp outs) (member-eq 'fn2-core outs) (pseudo-termp (cddr trip)))
        (acons f (all-fnnames (cddr trip)) acc) acc)))))
(defun fn2-qr-entry-core-callers (seeds entries acc)
 (declare (xargs :verify-guards nil))
 (if (atom entries) acc
  (fn2-qr-entry-core-callers seeds (cdr entries)
   (if (and (intersectp-eq seeds (cdar entries)) (not (member-eq (caar entries) acc)))
       (cons (caar entries) acc) acc))))
(defun fn2-qr-all-core-callers (seeds entries acc fuel)
 (declare (xargs :verify-guards nil :measure (nfix fuel)))
 (let ((next (fn2-qr-entry-core-callers (append seeds acc) entries acc)))
  (cond ((subsetp-eq next acc) acc)
        ((zp fuel) (cons :incomplete next))
        (t (fn2-qr-all-core-callers seeds entries next (- fuel 1))))))
(defun fn2-qr-face-after (f wrld)
 (declare (xargs :verify-guards nil))
 (fn2-bf-out (cons f (formals f wrld)) (getpropc f 'stobjs-out nil wrld) 'fn2-core))
(defun fn2-qr-face-obligation (f wrld)
 (declare (xargs :verify-guards nil))
 (let ((after (fn2-qr-face-after f wrld))
       (guard (getpropc f 'guard t wrld))
       (name (fn2-bf-name f "-QUERY-REFERENCES-ACCOUNTED")))
  `(defthm ,name
    (implies (and (fn2-core-query-reference-domainp fn2-core)
                  (fn2-core-query-counts-matchp fn2-core) ,guard)
             (and (fn2-core-query-reference-domainp ,after)
                  (fn2-core-query-counts-matchp ,after)))
    :rule-classes nil
    :hints (("Goal" :expand (,(cons f (formals f wrld))))))))
(defun fn2-qr-face-obligations (fs wrld)
 (declare (xargs :verify-guards nil))
 (if (atom fs) nil
  (cons (fn2-qr-face-obligation (car fs) wrld) (fn2-qr-face-obligations (cdr fs) wrld))))
(defun fn2-qr-writer-caller-map (writers entries)
 (declare (xargs :verify-guards nil))
 (if (atom writers) nil
  (cons (cons (car writers)
              (fn2-qr-entry-core-callers (list (car writers)) entries nil))
        (fn2-qr-writer-caller-map (cdr writers) entries))))
(make-event
 (let* ((wrld (w state))
        (pw (set-difference-eq (fn2-qr-world-writers 'fn2-pool wrld nil)
                              '(create-fn2-pool fn2-core-pool)))
        (dw (set-difference-eq (fn2-qr-world-writers 'fn2-id-decides wrld nil)
                              '(create-fn2-id-decides fn2-core-id-decides)))
        (seeds (append '(update-fn2-core-pool update-fn2-core-id-decides) pw dw))
        (entries (fn2-qr-core-body-entries wrld wrld nil))
        (faces (fn2-qr-all-core-callers seeds entries nil (+ 1 (len entries))))
        ; This bound is derived from the actual world, not a fixed lane cap.
        (fuel (+ 1 (len wrld) (* (len wrld) (len wrld))))
        (closure (fn2-bf-core-closure faces wrld nil fuel)))
  (if (member-eq :incomplete faces) '(assert-event nil)
  `(progn
    (defconst *fn2-qr-pool-writers* ',pw)
    (defconst *fn2-qr-descriptor-writers* ',dw)
    (defconst *fn2-qr-core-faces* ',faces)
    (defconst *fn2-qr-core-callee-closure* ',closure)
    (defconst *fn2-qr-pool-caller-map* ',(fn2-qr-writer-caller-map pw entries))
    (defconst *fn2-qr-descriptor-caller-map* ',(fn2-qr-writer-caller-map dw entries))
    (defconst *fn2-qr-unrun-face-obligations* ',(fn2-qr-face-obligations closure wrld))))))

; The inventory includes initialization and replay callers: they are not
; silently dropped from the whole world. Bootstrap needs its constructive
; empty-query/zero-count initialization theorem, not an unchanged-state
; frame. Replay sweep must consume the real release theorem or refuse an
; active query; metadata-only importer changes use typed key frames.
; Raw setters/byte loops are excluded ONLY as standalone served subjects;
; the caller maps above expose every core function reaching them. A full
; served invariant must discharge this complete obligation set and retain
; the actual guards at each call, not merely prove :start/:step/:cancel.
