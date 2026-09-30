(in-package "ACL2")
(include-book "../../books/replay-snapshot-cursor")
(defmacro rsct2 (n call) `(mv-let (a b) ,call (nth ,n (list a b))))
(defconst *rsct-a* (fn-stxk-make 0 0 0 3 '(1) '(2)))
(defconst *rsct-b* (fn-stxk-make 1 1 1 4 '(3) '(4)))
(defconst *rsct-start* (fn-rsc-begin 4 (list *rsct-a* *rsct-b*) '(7 5 9 17 :identity)))
; Complete literal antecedent/conclusion of actual one-step selection boundary.
(assert-event
 (let ((cursor *rsct-start*))
  (and (fn-rsc-invariantp cursor)
       (fn-rsc-invariantp (rsct2 1 (fn-rsc-step cursor)))
       (equal (fn-rsc-abstract (rsct2 1 (fn-rsc-step cursor)))
              (fn-rsc-abstract cursor))
       (eq (rsct2 0 (fn-rsc-step cursor)) :working)
       (equal (fn-rsc-at 2 (rsct2 1 (fn-rsc-step cursor))) (list *rsct-b*)))))
; Actual next step finishes with the first matching immutable snapshot.
(assert-event
 (let* ((first (rsct2 1 (fn-rsc-step *rsct-start*)))
        (second (rsct2 1 (fn-rsc-step first))))
  (and (eq (rsct2 0 (fn-rsc-step first)) :done)
       (eq (fn-rsc-at 0 second) :found)
       (equal (fn-rsc-at 3 second) *rsct-b*)
       (equal (fn-rsc-at 3 second) (fn-stxk-find 4 (list *rsct-a* *rsct-b*)))
       (equal (rsct2 1 (fn-rsc-step second)) second))))
; Exhaustion is a completed missing lookup, not a successful snapshot.
(assert-event
 (let* ((cursor (fn-rsc-begin 99 nil '(7 5 9 17 :identity)))
        (next (rsct2 1 (fn-rsc-step cursor))))
  (and (fn-rsc-invariantp cursor) (fn-rsc-invariantp next)
       (eq (fn-rsc-at 0 next) :done) (null (fn-rsc-at 3 next))
       (equal (fn-rsc-abstract next) (fn-stxk-find 99 nil)))))
; Corrupted-state hypothesis removal: preserve shape/phase/generation/source,
; violate carried typed snapshots; bypassing old deep recognizer would select
; a malformed candidate. This is not a provenance-establishment fixture.
(assert-event
 (let* ((bad (update-nth 4 :bad *rsct-b*))
        (cursor (fn-rsc-begin 4 (list bad) '(7 5 9 17 :identity)))
        (next (rsct2 1 (fn-rsc-step cursor))))
  (and (fn-rsc-widthp 5 cursor) (eq (fn-rsc-at 0 cursor) :seek)
       (equal (fn-stxk-keyring-generation bad) 4) (not (fn-stxk-p bad))
       (not (fn-rsc-invariantp cursor))
       (not (and (fn-rsc-invariantp next)
                 (equal (fn-rsc-abstract next) (fn-rsc-abstract cursor)))))))
; Actual initial replay establishes the carried predicate.
(assert-event (fn-rsc-typed-snapshotsp
 (fn-stxk-context-snapshots (fn-stxk-initial-context 0))))
; Complete typed-preservation antecedent and conclusion on an actual append.
(assert-event
 (let* ((ctx (fn-stxk-initial-context 0))
        (next (fn-replay-identity-step ctx *rsct-a*)))
  (and (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots ctx))
       (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots next))
       (eq (fn-stxk-context-kind next) :ok)
       (equal (fn-stxk-context-snapshots next) (list *rsct-a*)))))
; Corrupted-state removal of the sole typed-source hypothesis. Fault retains
; conflicting evidence, so a malformed old tail remains malformed.
(assert-event
 (let* ((bad (update-nth 4 :bad *rsct-b*))
        (ctx (fn-stxk-context :ok 0 (list bad) nil 4 nil))
        (next (fn-replay-identity-step ctx *rsct-a*)))
  (and (not (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots ctx)))
       (not (fn-rsc-typed-snapshotsp (fn-stxk-context-snapshots next))))))
