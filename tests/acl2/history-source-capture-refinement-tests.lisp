; Literal INTERNAL setup of registered metadata and actual STATE. These
; fixtures do not represent a physical constructor, funded public capture,
; native callback receipt, or atomic Store publication. Cancellation is
; reached through the actual issued-slot transition and actual cancel call.
(in-package "ACL2")
(include-book "../../books/history-source-capture-refinement")
(defconst *hsct-source* '(:history-source 41 42 43 nil 0 1 1 44))
(defconst *hsct-parent* '(:history-installed 41 42 43 44 7))
(defconst *hsct-epoch* '(:history-epoch 42 7 :issued :live t 1 0 nil nil :debt nil))
(defconst *hsct-ledger* (fn-prl-make '(10000 10000 10 10 100)))
(defconst *hsct-issued* (mv-list 4 (fn-hhc-admit *hsct-ledger* nil 7 *hsct-source* '(128 0 0 0 1))))
(defconst *hsct-token* (fn-hhc-at 1 (nth 1 *hsct-issued*)))
; Exactly the complete conjunction exported by the source attribution law.
(defmacro hsct-source-conclusion (answer)
 `(and (equal (nth 1 ,answer) (fn-hep-current fn-history-backing))
       (fn-hhc-sourcep (fn-hep-current fn-history-backing))
       (posp (fn-hhc-at 2 (fn-hep-current fn-history-backing)))
       (natp (fn-owner-canonical-epoch state))
       (fn-hhc-widthp (fn-owner-history-publication state) 6)
       (equal (fn-hhc-at 0 (fn-owner-history-publication state)) :history-installed)
       (equal (fn-hhc-at 1 (fn-owner-history-publication state)) (fn-hhc-at 1 (fn-hep-current fn-history-backing)))
       (equal (fn-hhc-at 2 (fn-owner-history-publication state)) (fn-hhc-at 2 (fn-hep-current fn-history-backing)))
       (equal (fn-hhc-at 3 (fn-owner-history-publication state)) (fn-hhc-at 3 (fn-hep-current fn-history-backing)))
       (equal (fn-hhc-at 4 (fn-owner-history-publication state)) (fn-hhc-at 8 (fn-hep-current fn-history-backing)))
       (equal (fn-hhc-at 5 (fn-owner-history-publication state)) (fn-owner-canonical-epoch state))))
(defun hsct-source-fixture (case fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :mode :program))
 (let* ((fn-history-backing (update-fn-hep-installed-source
             (if (eq case :epoch-remove-source) nil *hsct-source*) fn-history-backing))
        (state (f-put-global 'fn-owner-canonical-epoch
                (if (member-eq case '(:epoch-positive :epoch-remove-parent :epoch-remove-source)) 8 7) state))
        (state (f-put-global 'fn-owner-history-publication
                (if (member-eq case '(:source-remove-status :epoch-remove-parent)) nil *hsct-parent*) state))
        (answer (mv-list 2 (fn-owner-history-source fn-history-backing state)))
        (parent (fn-owner-history-publication state))
        (source (fn-hep-current fn-history-backing))
        (mismatch (not (equal (fn-hhc-at 5 parent) (fn-owner-canonical-epoch state))))
        (refused (equal answer '(:recovery-required nil)))
        (ok (case case
          (:source-positive (and (eq (car answer) :source) (hsct-source-conclusion answer)))
          (:source-remove-status (and (not (eq (car answer) :source))
                                     (not (hsct-source-conclusion answer))))
          (:epoch-positive (and parent source mismatch refused))
          (:epoch-remove-parent (and (not parent) source mismatch (not refused)))
          (:epoch-remove-source (and parent (not source) mismatch (not refused)))
          (:epoch-remove-mismatch (and parent source (not mismatch) (not refused)))
          (otherwise nil))))
  (mv ok fn-history-backing state)))
(defun hsct-source-run (case state)
 (declare (xargs :stobjs state :mode :program))
 (with-local-stobj fn-history-backing
  (mv-let (ok fn-history-backing state) (hsct-source-fixture case fn-history-backing state)
   (mv ok state))))
; Reachable INTERNAL positive: complete attribution antecedent/conclusion.
(assert-event
 (mv-let (ok state) (hsct-source-run :source-positive state) (mv ok state))
 :stobjs-out '(nil state))
; Hypothesis removal: missing parent prevents :source and fails complete attribution.
(assert-event
 (mv-let (ok state) (hsct-source-run :source-remove-status state) (mv ok state))
 :stobjs-out '(nil state))
; Mutation positive: parent from prior canonical epoch refuses exact result.
(assert-event
 (mv-let (ok state) (hsct-source-run :epoch-positive state) (mv ok state))
 :stobjs-out '(nil state))
; Hypothesis removal: parent absent; every retained hypothesis checked.
(assert-event
 (mv-let (ok state) (hsct-source-run :epoch-remove-parent state) (mv ok state))
 :stobjs-out '(nil state))
; Hypothesis removal: backing source absent; every retained hypothesis checked.
(assert-event
 (mv-let (ok state) (hsct-source-run :epoch-remove-source state) (mv ok state))
 :stobjs-out '(nil state))
; Hypothesis removal: matching current parent permits :source.
(assert-event
 (mv-let (ok state) (hsct-source-run :epoch-remove-mismatch state) (mv ok state))
 :stobjs-out '(nil state))
; Complete no-effects conclusion is proved over STATE by the keystone;
; its executable copy observes the publication/epoch/capture/read globals.
; No selected page/provider call is reachable after actual cancellation.
(defun hsct-cancel-fixture (cancelp fn-history-backing state)
 (declare (xargs :stobjs (fn-history-backing state) :mode :program))
 (let* ((fn-history-backing (update-fn-hep-installed-source *hsct-source* fn-history-backing))
        (fn-history-backing (update-fn-hep-epoch *hsct-epoch* fn-history-backing))
        (fn-history-backing (update-fn-hep-capture (list *hsct-token* *hsct-source*) fn-history-backing))
        (state (f-put-global 'fn-owner-canonical-epoch 7 state))
        (state (fn-owner-history-keep-capture (nth 3 *hsct-issued*) state))
        (state (f-put-global 'fn-owner-history-read nil state)))
  (mv-let (started state) (fn-owner-history-read-begin *hsct-token* 0 fn-history-backing state)
   (let* ((ready (and (eq (nth 0 *hsct-issued*) :captured)
                      (eq started :history-read-started)
                      (fn-hep-capture-livep *hsct-source* *hsct-token* fn-history-backing)))
          (state (if cancelp (fn-owner-history-cancel *hsct-token* state) state))
          (antecedent (not (equal (fn-hhc-at 5 (fn-owner-history-capture-slot state)) :retained)))
          (old-globals (list (fn-owner-history-publication state)
                             (fn-owner-canonical-epoch state)
                             (fn-owner-history-capture-slot state)
                             (fn-owner-history-read-slot state)))
          (slot (fn-owner-history-capture-slot state))
          (reader (fn-owner-history-read-slot state)))
    (mv-let (word row left state) (fn-owner-history-read-step 0 fn-history-backing state)
     (let ((conclusion (and (eq word :history-source-stale) (null row) (equal left 0)
                             (equal (list (fn-owner-history-publication state)
                                          (fn-owner-canonical-epoch state)
                                          (fn-owner-history-capture-slot state)
                                          (fn-owner-history-read-slot state)) old-globals))))
      (mv (and ready
               (if cancelp
                (and antecedent conclusion
                     (equal slot (fn-owner-history-capture-slot state))
                     (equal reader (fn-owner-history-read-slot state))
                     (fn-hep-capture-livep *hsct-source* *hsct-token* fn-history-backing)
                     (eq (fn-owner-history-reset-status state) :history-source-held))
                (and (not antecedent) (not conclusion) (eq word :yield)
                     (equal (list (fn-owner-history-publication state)
                                          (fn-owner-canonical-epoch state)
                                          (fn-owner-history-capture-slot state)
                                          (fn-owner-history-read-slot state)) old-globals))))
          fn-history-backing state)))))))
(defun hsct-cancel-run (cancelp state)
 (declare (xargs :stobjs state :mode :program))
 (with-local-stobj fn-history-backing
  (mv-let (ok fn-history-backing state) (hsct-cancel-fixture cancelp fn-history-backing state)
   (mv ok state))))
; Actual cancellation positive; pin, slot and read aliases remain held.
(assert-event
 (mv-let (ok state) (hsct-cancel-run t state) (mv ok state))
 :stobjs-out '(nil state))
; Hypothesis removal: registered retained read with fuel zero yields unchanged.
(assert-event
 (mv-let (ok state) (hsct-cancel-run nil state) (mv ok state))
 :stobjs-out '(nil state))
