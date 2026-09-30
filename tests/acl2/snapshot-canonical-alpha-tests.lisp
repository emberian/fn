; PRF-1115: canonical history alpha, including the independently held
; composite payload. Physical copy/decoder correspondence remains external.
(in-package "ACL2")
(include-book "../../books/snapshot-canonical-alpha")
(include-book "../../books/codec-attach")
(include-book "snapshot-node-alpha-tests")
(include-book "statement-recover-stream-tests")
(defconst *osac-one*
  (fn-record-make 0 0 0 "<one@example>" '(1 2 3) '("fn.test")
                  "one" "c1" "r1" 1 841000000))
(defconst *osac-two*
  (fn-record-make 1 1 0 "<two@example>" '(4 5) '("fn.test")
                  "two" "c2" "r2" 1 841000001))
(defconst *osac-three*
  (fn-record-make 2 2 0 "<three@example>" '(6 7) '("fn.test")
                  "three" "c3" "r3" 1 841000002))
(defconst *osac-stxa*
  (fn-stxa-make 2 2 0 9 '(112) (fn-record-string-octets "c3")
                (fn-record-encode-impl *osac-three*)
                (fn-stxe-encode
                 (fn-stxe-make 2 2 0 "<three@example>" :unverified
                                *fn-stx-token-signature* 9 '(112)))))
(defun osac-intern-with-orphan ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (let ((fn-arena (fn-arena-seal-list '(99) fn-arena)))
        (fn-intern-events (list *osac-one* *osac-two* *osac-stxa*) nil 9 fn-arena))
      rows)))
(make-event `(defconst *osac-rows* ',(osac-intern-with-orphan)))
(defconst *osac-source* '((99) (1 2 3) (4 5) (6 7)))
(defconst *osac-target* '((1 2 3) (4 5) (6 7)))
(defconst *osac-canonical* (fn-orm-capture *osac-rows* 0))

(defthm osac-canonical-complete-history-alpha-positive-tooth
  (and (fn-orm-rowsp *osac-rows*) (natp 0)
       (equal (len *osac-rows*) 3)
       (fn-held-p (car *osac-rows*))
       (fn-hstxa-p (nth 2 *osac-rows*))
       (not (equal *osac-rows* *osac-canonical*))
       (fn-osa-payload-map-p *osac-rows* 0 *osac-source* *osac-target*)
       (equal (fn-osa-row-alphas *osac-canonical* *osac-target*)
              (fn-osa-row-alphas *osac-rows* *osac-source*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osa-payload-map-p fn-osa-row-alphas
                                     fn-orm-retained-alpha fn-orm-payload-bytes
                                     fn-orm-capture fn-row-bytes))))

; Remove only physical payload correspondence. The changed bytes belong to
; the composite-held ARTICLE, which fn-row-wire-of alone would miss.
(defthm osac-wrong-composite-payload-map-tooth
  (and (fn-orm-rowsp *osac-rows*) (natp 0)
       (not (fn-osa-payload-map-p *osac-rows* 0 *osac-source*
                                 '((1 2 3) (4 5) (88))))
       (not (equal (fn-osa-row-alphas *osac-canonical* '((1 2 3) (4 5) (88)))
                   (fn-osa-row-alphas *osac-rows* *osac-source*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osa-payload-map-p fn-osa-row-alphas
                                     fn-orm-retained-alpha fn-orm-payload-bytes
                                     fn-orm-capture fn-row-bytes))))

(assert-event
  (and (fn-orm-rowsp *osac-rows*) (natp 0)
       (equal (len (fn-sn-row-verdicts *osac-rows*)) 3)
       (equal (fn-sn-index-fold *osac-canonical* (fn-stx-index-empty))
              (fn-sn-index-fold *osac-rows* (fn-stx-index-empty)))
       (equal (fn-sn-row-verdicts-fold *osac-canonical* nil)
              (fn-sn-row-verdicts-fold *osac-rows* nil)))
)

; Complete consumer result across mixed durable metadata and a relocated
; composite-held ARTICLE. The account, scope and acknowledged cursor survive.
(defconst *osac-cp-boot* (fn-cpe-make 0 0 0 '(:bootstrap (1) (2))))
(defconst *osac-cp-register* (fn-cpe-make 1 1 1 '(:register (3) (4) (5) 1 1 1)))
(defconst *osac-cp-cursor* (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 2))
(defconst *osac-cp-ack* (fn-cpe-make 3 3 3 (list :ack *osac-cp-cursor*)))
(defconst *osac-cp-rows*
  (list *osac-cp-boot* *osac-cp-register* (nth 2 *osac-rows*) *osac-cp-ack*))
(assert-event
 (let* ((canonical (fn-orm-capture *osac-cp-rows* 0))
        (source-result (fn-cpe-projection-replay nil *osac-cp-rows* 0)))
   (and (fn-orm-rowsp *osac-cp-rows*) (natp 0)
        (not (equal canonical *osac-cp-rows*))
        (equal (car source-result) :ok)
        (fn-cp-statep (cadr source-result))
        (equal (nth 7 (fn-cp-find '(3) (nth 5 (cadr source-result)))) 2)
        (equal (fn-cpe-projection-replay nil canonical 0) source-result))))
; Hypothesis removal: a negative target handle corrupts the retained row.
(assert-event
 (with-guard-checking :none
   (and (fn-orm-rowsp *osac-cp-rows*) (not (natp -1))
        (not (equal (fn-cpe-projection-replay
                      nil (fn-orm-capture *osac-cp-rows* -1) 0)
                     (fn-cpe-projection-replay nil *osac-cp-rows* 0))))))
; Corrupted-state row-validity removal: remapping repairs an invalid handle,
; so replay refusal differs from the valid reconstructed ARTICLE result.
(assert-event
 (with-guard-checking :none
   (let ((rows (list (update-nth 4 -1 (car *osac-rows*)))))
     (and (not (fn-orm-rowsp rows)) (natp 0)
          (not (equal (fn-cpe-projection-replay nil (fn-orm-capture rows 0) 0)
                       (fn-cpe-projection-replay nil rows 0)))))))

; Full topic replay keeps the committed administrator and accepted statement,
; not only the journal coordinate. The composite's held payload relocates.
(defconst *osac-topic-admin*
  (list :topic-admin-install 0 0 0 1000 (make-list 32 :initial-element 7)))
(defconst *osac-topic-rows*
  (list *osac-topic-admin* (nth 1 *osac-rows*) (nth 2 *osac-rows*)))
(assert-event
 (let* ((canonical (fn-orm-capture *osac-topic-rows* 0))
        (original (fn-th-prefix-project *osac-topic-rows*)))
   (and (fn-orm-rowsp *osac-topic-rows*) (natp 0)
        (not (equal canonical *osac-topic-rows*))
        (equal (fn-th-at 0 original) :ok)
        (consp (fn-th-at 3 original))
        (equal (fn-th-at 5 original) *osac-topic-admin*)
        (equal (fn-th-prefix-project canonical) original))))
; Logical hypothesis removal: negative target handle invalidates the row.
(assert-event
 (with-guard-checking :none
  (and (fn-orm-rowsp *osac-topic-rows*) (not (natp -1))
       (not (equal (fn-th-prefix-project (fn-orm-capture *osac-topic-rows* -1))
                    (fn-th-prefix-project *osac-topic-rows*))))))
; Corrupted-state row-validity removal: remap repairs a negative source handle.
(assert-event
 (with-guard-checking :none
  (let ((rows (list (update-nth 4 -1 (car *osac-rows*)))))
   (and (not (fn-orm-rowsp rows)) (natp 0)
        (not (equal (fn-th-prefix-project (fn-orm-capture rows 0))
                     (fn-th-prefix-project rows)))))))

; The actual sequential recovery/intern worker produces valid configured
; history with two key generations. A prior unreferenced arena payload makes
; canonical handles differ, as happens after a discarded physical allocation.
(defun osac-identity-in (fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let* ((fn-arena (fn-arena-seal-list '(99) fn-arena))
        (seed (fn-ssr-seed (fn-stxk-initial-context 0))))
  (mv-let (acc fn-arena)
   (fn-ssr-intern-step seed (append *ssrt-a* *ssrt-b*) nil nil :resident nil fn-arena)
   (mv (fn-ssr-rows acc) fn-arena))))
(defun osac-identity-rows ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (rows fn-arena) (osac-identity-in fn-arena) rows)))
(make-event `(defconst *osac-id-rows* ',(osac-identity-rows)))
(defconst *osac-id-configs*
 (list *fn-cfg-default-record*
       (fn-cfg-record-make 1 0 2
          (list (fn-cfg-create-group "example" *fn-cfg-default-policy-id*))
          *fn-cfg-default-stamp*)))
(make-event `(defconst *osac-id-open*
 ',(fn-cpo-open-observed *osac-id-configs* 4 *osac-id-rows*)))
(make-event `(defconst *osac-id-ready*
 ',(fn-snrt-run (fn-sn-open-state *osac-id-open*)
     '((:io :recovery-barrier :ok) (:io :recovery-barrier :ok)
       (:io :recovery-barrier :ok)))))
(assert-event
 (let ((original (fn-replay-identity *osac-id-rows*)))
  (and (fn-orm-rowsp *osac-id-rows*) (natp 0)
       (fn-sn-open-okp *osac-id-open*)
       (fn-osr-retainedp *osac-id-ready*)
       (equal (fn-sf-phase (fn-sn-files *osac-id-ready*)) :ready)
       (equal (fn-sf-records (fn-sn-files (fn-osr-capture *osac-id-ready*)))
              *osac-id-rows*)
       (not (equal (fn-orm-capture *osac-id-rows* 0) *osac-id-rows*))
       (equal (fn-stxk-context-kind original) :ok)
       (equal (len (fn-stxk-context-snapshots original)) 2)
       (equal (fn-stxk-context-current-generation original) 2)
       (equal (fn-replay-identity (fn-orm-capture *osac-id-rows* 0)) original))))
; Complete topic result also survives this actual ready captured history.
(assert-event
 (and (fn-orm-rowsp *osac-id-rows*) (natp 0)
      (fn-osr-retainedp *osac-id-ready*)
      (equal (fn-sf-phase (fn-sn-files *osac-id-ready*)) :ready)
      (equal (fn-th-prefix-project (fn-orm-capture *osac-id-rows* 0))
             (fn-th-prefix-project *osac-id-rows*))))
; Logical natural-handle removal, retaining valid actual source rows.
(assert-event
 (with-guard-checking :none
  (and (fn-orm-rowsp *osac-id-rows*) (not (natp -1))
       (not (equal (fn-replay-identity (fn-orm-capture *osac-id-rows* -1))
                    (fn-replay-identity *osac-id-rows*))))))
; Corrupted-state row-validity removal: remap repairs the invalid source handle.
(assert-event
 (with-guard-checking :none
  (let ((rows (list (update-nth 4 -1 (car *osac-rows*)))))
   (and (not (fn-orm-rowsp rows)) (natp 0)
        (not (equal (fn-replay-identity (fn-orm-capture rows 0))
                     (fn-replay-identity rows)))))))
