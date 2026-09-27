; Reachable Store outcomes and teeth for the byte-identity decision
; (books/store-node-existing-invariants.lisp, fn-sn-action-over) and the
; entry the host calls (books/store-intern.lisp fn-store-existing-action).
; by specification: the flip -- the held payload is a handle, so
; fn-sn-action-over is the specification over the WIRE view: its
; outcomes are asserted over alpha of the Store's articles (the bytes under
; each handle, books/store-existing-alpha.lisp fn-sn-action-over over
; fn-sn-alpha-articles, which fn-store-existing-action-refines-byte-identity-
; over-alpha relates to the entry).
(in-package "ACL2")
(include-book "../../books/store-node-existing-invariants")
(include-book "../../books/store-existing-alpha")
(include-book "../../books/codec-attach")
(include-book "held-rows-tests")
(include-book "must-fail-checked")

(defconst *snex-groups* '("fn.letters" "fn.test"))
(defconst *snex-record-wire*
  (fn-record-make 0 0 0 "<held@example>" '(65 66) *snex-groups*
                  "snex-pin" "snex-subject" "snex-release" 2 841000000))
; The store takes the held row (records-flip): the record interned on a
; fresh arena, its payload the handle 0.
(defconst *snex-record* (car (fn-hrt-rows (list *snex-record-wire*) nil 0)))
(assert-event (fn-held-p *snex-record*))
(defconst *snex-reserved*
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io
              (fn-sn-initial *snex-groups* 10) :start-frontier nil)
              :frontier-file :ok) :frontier-replace :ok)
              :frontier-directory :ok))
(defconst *snex-prepared* (fn-sn-prepare *snex-reserved* *snex-record*))
(defconst *snex-finished*
  (fn-sn-finish
   (fn-sn-io (fn-sn-io (fn-sn-io *snex-prepared* :record-file :ok)
                        :record-link :ok)
             :record-directory :ok)))

(assert-event (fn-sn-statep *snex-finished*))
(assert-event
 (fn-find-article "<held@example>"
                  (fn-state-articles
                   (fn-node-acceptance (fn-sn-node *snex-finished*)))))
;; The byte-identity decision over alpha of S's articles, read through the
;; arena that interned PRIOR.
(defun snex-sn-in (prior msgid payload groups s fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (mv (fn-sn-action-over msgid payload groups (fn-sn-alpha-articles s fn-arena))
        fn-arena)))
(defun snex-sn (msgid payload groups s)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena) (snex-sn-in (list *snex-record-wire*) msgid payload groups s fn-arena)
      r)))
; Over the live Store's own articles (handles) a byte-identical resend is no
; duplicate, which is why the outcomes below are over alpha (and why the
; store-shaped twin fn-sn-existing-action was retired, PKT-EG-4).
(assert-event
 (equal (fn-sn-action-over "<held@example>" '(65 66) *snex-groups*
                           (fn-state-articles (fn-node-acceptance
                                               (fn-sn-node *snex-finished*))))
        :conflict))
(assert-event (equal (snex-sn
                      "<held@example>" '(65 66) *snex-groups* *snex-finished*)
                     :duplicate))
(assert-event (equal (snex-sn
                      "<held@example>" '(99) *snex-groups* *snex-finished*)
                     :conflict))
(assert-event (equal (snex-sn
                      "<held@example>" '(65 66) '("fn.letters") *snex-finished*)
                     :conflict))
(assert-event (null (snex-sn
                     "<missing@example>" '(65 66) *snex-groups* *snex-finished*)))

; Each deleted premise makes the corresponding outcome false on the same
; committed article: payload equality, group equality, or a held binding.
(must-fail-checked
 (assert-event
  (equal (snex-sn
          "<held@example>" '(99) *snex-groups* *snex-finished*)
         :duplicate)))
(must-fail-checked
 (assert-event
  (equal (snex-sn
          "<held@example>" '(65 66) '("fn.letters") *snex-finished*)
         :duplicate)))
(must-fail-checked
 (assert-event
  (equal (snex-sn
          "<missing@example>" '(65 66) *snex-groups* *snex-finished*)
         :duplicate)))
; A difference without a held Message-ID is missing, not a conflict.
(must-fail-checked
 (assert-event
  (equal (snex-sn
          "<missing@example>" '(99) *snex-groups* *snex-finished*)
         :conflict)))

; The same outcomes and teeth through the entry the host calls after the
; flip (store-intern fn-store-existing-action, here fn-hrt-existing-action
; over the arena that interned the store's record): the held article's
; payload is a handle, and the verdict compares the offered octets with the
; bytes under it.
(defconst *snex-prior* (list *snex-record-wire*))
(assert-event (equal (fn-hrt-existing-action
                      *snex-prior* "<held@example>" '(65 66) *snex-groups* *snex-finished*)
                     :duplicate))
(assert-event (equal (fn-hrt-existing-action
                      *snex-prior* "<held@example>" '(99) *snex-groups* *snex-finished*)
                     :conflict))
(assert-event (equal (fn-hrt-existing-action
                      *snex-prior* "<held@example>" '(65 66) '("fn.letters") *snex-finished*)
                     :conflict))
(assert-event (null (fn-hrt-existing-action
                     *snex-prior* "<missing@example>" '(65 66) *snex-groups* *snex-finished*)))
(must-fail-checked
 (assert-event
  (equal (fn-hrt-existing-action
          *snex-prior* "<held@example>" '(99) *snex-groups* *snex-finished*)
         :duplicate)))
(must-fail-checked
 (assert-event
  (equal (fn-hrt-existing-action
          *snex-prior* "<held@example>" '(65 66) '("fn.letters") *snex-finished*)
         :duplicate)))
(must-fail-checked
 (assert-event
  (equal (fn-hrt-existing-action
          *snex-prior* "<missing@example>" '(65 66) *snex-groups* *snex-finished*)
         :duplicate)))
(must-fail-checked
 (assert-event
  (equal (fn-hrt-existing-action
          *snex-prior* "<missing@example>" '(99) *snex-groups* *snex-finished*)
         :conflict)))
