; BEGIN retains the actual reserved Store and its original prefix node,
; before intern/prepare/stage. Never reconstruct the prefix from a staged node.
; Internal pre-call registration for canonical admission preparation.
; Not a native export. The complete semantic producer and its installed
; operation allowance must precede the invocation of this allocating entry.
(in-package "ACL2")
(include-book "owner-host")
(include-book "../books/admission-preparation-intent")
(include-book "../books/owner-canonical-read-state")
(include-book "../books/store-events-carried")
(include-book "../books/history-semantic-writer")
(include-book "../books/admission-semantic-exclusion")

(defun fn-owner-admission-prepare-intent (state)
 (declare (xargs :stobjs state :mode :program
  :guard (and (boundp-global 'fn-owner state)
              (fn-sn-statep (fn-owner-store state)))))
 (let* ((current (fn-apr-owner-current state))
        (token (fn-prl-nth 0 current))
        (base-store (fn-owner-store state))
        (files (fn-sn-files base-store))
        (frontier (fn-sf-frontier files))
        (canonical (fn-owner-canonical-state state))
        (epoch (fn-owner-canonical-epoch state))
        (count (fn-sf-records-count files))
        (parent (and (boundp-global 'fn-owner-history-publication state)
                     (f-get-global 'fn-owner-history-publication state)))
        (config (fn-owner-config state))
        (obligation-view (fn-owner-obligation-view state))
        (reader-view (fn-own-view (fn-owner-core state)))
        (posting-config (fn-own-config (fn-owner-core state)))
        (prior (and (boundp-global 'fn-owner-canonical-admission-executor state)
                    (f-get-global 'fn-owner-canonical-admission-executor state))))
  (cond
   ((fn-owner-admission-semantic-busy-p state)
    (mv :semantic-writer-busy token state))
   ; Re-entry across a raw escape must not execute the semantic producer
   ; twice. Neither the reservation nor its retained source is discarded.
   (prior (mv :admission-recovery-required token state))
   ((not (and (fn-hsw-parentp parent)
               (equal (fn-prl-nth 5 parent) epoch)
               (posp frontier)
               (fn-api-reserved-coordinatesp current canonical epoch count
                 (fn-sf-phase files) count (1- frontier))))
    (mv :stale token state))
   (t
    (let ((state (f-put-global 'fn-owner-canonical-admission-executor
                  (list :admission-prepare-intent token epoch count
                        (cons count (1- frontier))
                        base-store canonical current)
                  state)))
     (let ((state (f-put-global 'fn-owner-history-semantic-source
                    (list :history-semantic-source token parent config) state)))
       (let ((state (f-put-global 'fn-owner-history-semantic-obligation-base
                     (list :history-obligation-base token obligation-view) state)))
        (let ((state (f-put-global 'fn-owner-history-semantic-reader-base
                       (list :history-reader-base token reader-view posting-config) state)))
         (mv :intent-retained token state)))))))))
