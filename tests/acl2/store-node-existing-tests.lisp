; Reachable Store outcomes and teeth for the actual host-called decision.
(in-package "ACL2")
(include-book "../../books/store-node-existing-invariants")
(include-book "../../books/codec-attach")
(include-book "held-rows-tests")
(include-book "std/testing/must-fail" :dir :system)

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
(assert-event (equal (fn-sn-existing-action
                      "<held@example>" '(65 66) *snex-groups* *snex-finished*)
                     :duplicate))
(assert-event (equal (fn-sn-existing-action
                      "<held@example>" '(99) *snex-groups* *snex-finished*)
                     :conflict))
(assert-event (equal (fn-sn-existing-action
                      "<held@example>" '(65 66) '("fn.letters") *snex-finished*)
                     :conflict))
(assert-event (null (fn-sn-existing-action
                     "<missing@example>" '(65 66) *snex-groups* *snex-finished*)))

; Each deleted premise makes the corresponding outcome false on the same
; committed article: payload equality, group equality, or a held binding.
(must-fail
 (assert-event
  (equal (fn-sn-existing-action
          "<held@example>" '(99) *snex-groups* *snex-finished*)
         :duplicate)))
(must-fail
 (assert-event
  (equal (fn-sn-existing-action
          "<held@example>" '(65 66) '("fn.letters") *snex-finished*)
         :duplicate)))
(must-fail
 (assert-event
  (equal (fn-sn-existing-action
          "<missing@example>" '(65 66) *snex-groups* *snex-finished*)
         :duplicate)))
; A difference without a held Message-ID is missing, not a conflict.
(must-fail
 (assert-event
  (equal (fn-sn-existing-action
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
(must-fail
 (assert-event
  (equal (fn-hrt-existing-action
          *snex-prior* "<held@example>" '(99) *snex-groups* *snex-finished*)
         :duplicate)))
(must-fail
 (assert-event
  (equal (fn-hrt-existing-action
          *snex-prior* "<held@example>" '(65 66) '("fn.letters") *snex-finished*)
         :duplicate)))
(must-fail
 (assert-event
  (equal (fn-hrt-existing-action
          *snex-prior* "<missing@example>" '(65 66) *snex-groups* *snex-finished*)
         :duplicate)))
(must-fail
 (assert-event
  (equal (fn-hrt-existing-action
          *snex-prior* "<missing@example>" '(99) *snex-groups* *snex-finished*)
         :conflict)))
