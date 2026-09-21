; Teeth for K1 to K4 (crash model v2, section 3.3).
;
; This book retains the original K1/K2 negative witnesses. The concrete
; metadata attachments now supply a reachable positive witness in
; tests/acl2/byte-store-relation-tests.lisp: a complete first allocation
; reaches a related rename window, and legal old/new crash choices produce
; distinct, successfully scanned frontier images. A local constructor lemma
; connects its executable choice checks to the existential crash predicate.
; Nonempty-history executable witnesses still need the transaction-name
; attachment. The tests below use the early config-entry check and therefore
; do not require concrete codec attachments.
;
; The two hypotheses are (fn-bs-store-relation bs ks) and
; (fn-bs-crash-imagep bs image).  Each tooth below drops exactly one.

(in-package "ACL2")
(include-book "../../books/byte-store-keystones")
(include-book "../../books/byte-store-programs")

; -----------------------------------------------------------------------------
; The anchor: the clause each tooth violates is TRUE of the store the
; programs run on, so neither tooth is a statement about an impossible
; store (tools/teeth_check.py's predicate-never-anchored).
(assert-event (fn-bs-statep *fn-bs-initialized-store*))
(assert-event (fn-bs-inop (fn-bs-lookup *fn-bs-initialized-store*
                                        :root *fn-bs-scan-config-name*)))
(assert-event (fn-bs-inop (fn-bs-lookup *fn-bs-initialized-store*
                                        :root *fn-bs-scan-frontier-name*)))
(assert-event (fn-bs-dir-quietp *fn-bs-initialized-store* :root))

; -----------------------------------------------------------------------------
; Tooth 1: without (fn-bs-store-relation bs ks).
;
; A store that holds the allocator frontier and an empty transaction
; directory but NO config entry.  It is a well-formed byte store, and
; (fn-bs-crash s nil) is an admissible image of it
; (fn-bs-lose-everything-is-an-admissible-image), so the crash-image
; hypothesis holds -- and the scan of that image faults at :config.  The
; relation's config clause is what K1 needs and nothing else supplies it.
(defconst *bsk-no-config*
  (fn-bs-make 4
              (list (cons 1 *fn-bs-sample-frontier*))
              (list (cons :root (list (cons *fn-bs-scan-frontier-name* 1)))
                    (cons :transactions nil))
              nil 2))
(assert-event (fn-bs-statep *bsk-no-config*))
(assert-event (not (fn-bs-store-relation *bsk-no-config* (fn-sf-initial-state))))
(defconst *bsk-no-config-image* (fn-bs-crash *bsk-no-config* nil))
(assert-event (equal (fn-bs-scan-store *bsk-no-config-image*)
                     (list :fault :config)))
(assert-event (not (fn-bs-scan-okp (fn-bs-scan-store *bsk-no-config-image*))))

; -----------------------------------------------------------------------------
; Tooth 2: without (fn-bs-crash-imagep bs image).
;
; The initialized store with the config entry removed from :root.  The
; store's :root is quiet, so by fn-bs-crash-keeps-quiet-directory every
; admissible image of it has :root's entries unchanged -- this image's do
; not, so no choice list produces it, which is exactly why the hypothesis
; is needed.  Its scan faults at :config.
(defconst *bsk-forged*
  (fn-bs-make (fn-bs-unit *fn-bs-initialized-store*)
              (fn-bs-inodes *fn-bs-initialized-store*)
              (list (cons :parent (list (cons "store" :root)))
                    (cons :root (list (cons *fn-bs-scan-frontier-name* 1)))
                    (cons :transactions nil)
                    (cons :staging nil))
              nil
              (fn-bs-next-ino *fn-bs-initialized-store*)))
(assert-event (fn-bs-statep *bsk-forged*))
(assert-event (not (equal (assoc-equal :root (fn-bs-dirs *bsk-forged*))
                          (assoc-equal :root (fn-bs-dirs
                                              *fn-bs-initialized-store*)))))
(assert-event (equal (fn-bs-scan-store *bsk-forged*) (list :fault :config)))
(assert-event (not (fn-bs-scan-okp (fn-bs-scan-store *bsk-forged*))))

; -----------------------------------------------------------------------------
; K4's scope.  fn-bs-acknowledged-record-survives-byte-crash has no
; reachable instance INSIDE the recovery window, because
; fn-bs-replay-matches-scan carries (equal (fn-sf-successes ks) nil) there
; and the theorem's fourth hypothesis is a member of that list; its live
; instances are the publish window, where the composed runs of
; tests/acl2/byte-store-tests.lisp reach an acknowledged state.  What
; covers the recovery window is fn-bs-crash-image-reopens, which carries no
; success hypothesis at all.  The two phase sets are disjoint and that is
; evaluable here.
(assert-event (not (fn-bs-replay-visiblep (fn-sf-initial-state))))
(assert-event (fn-bs-replay-visiblep
               (fn-sf-make :replaying 0 nil nil nil nil nil 0)))
