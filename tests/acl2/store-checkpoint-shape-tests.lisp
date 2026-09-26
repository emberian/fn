; Teeth for books/store-checkpoint-shape.lisp (PKT-395): an index of an
; older shape is refused by name; this image's own publication is not.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/store-checkpoint-shape")
(include-book "store-checkpoint-open-tests")

; Reachable witness: store-checkpoint-open-tests' recovery image, the
; capture of its first event extended over the second (the value a host
; open extends and fn-store-sco-publish-octets freezes).  The file carries
; the count 2, not the records, and thaws back to the value.
(defconst *scs-t-c*
  (fn-sco-extend (fn-sco-capture *sco-t-configs* *sco-t-prefix*)
                 *sco-t-configs* *sco-t-suffix*))
(defconst *scs-t-f* (fn-sco-freeze *scs-t-c*))
(assert-event (true-listp *sco-t-suffix*))
(assert-event (equal (fn-sco-at 1 *scs-t-f*) 2))
(assert-event (equal (fn-sco-records *scs-t-c*) *sco-t-events*))
(assert-event (fn-sco-index-shape-okp *scs-t-c*))
(assert-event (equal (fn-sco-thaw-checked *scs-t-f*) (list :ok *scs-t-c*)))

; fn-sco-thaw-checked-accepts-own-publication without (true-listp suffix):
; a suffix that is an atom makes a value whose record slot is a natural,
; which the thaw reads as a count (labelled: the host's suffix is always a
; decoded record list).
(defconst *scs-t-atom-c*
  (fn-sco-extend (fn-sco-capture *sco-t-configs* nil) *sco-t-configs* 5))
(assert-event (not (true-listp 5)))
(assert-event (not (equal (fn-sco-thaw-checked (fn-sco-freeze *scs-t-atom-c*))
                          (list :ok *scs-t-atom-c*))))
(must-fail
 (defthm fn-scs-t-own-publication-without-true-listp
   (equal (fn-sco-thaw-checked (fn-sco-freeze *scs-t-atom-c*))
          (list :ok *scs-t-atom-c*))))

; The older shapes (corrupted relative to this image; written by older
; images).  The pair (SEQ-TRIE . MSGID-TRIE) of a249a699..d0df09ed: the
; plain thaw reads the RIGHT records out of it, which is why that open used
; to succeed with a non-corresponding index; the checked thaw refuses it.
(defconst *scs-t-index* (fn-sco-event-index *scs-t-f*))
(defconst *scs-t-pair* (cons (car *scs-t-index*) (cadr *scs-t-index*)))
(defmacro scs-t-with-index (f idx)
  `(update-nth 6 ,idx ,f))
(defconst *scs-t-pair-f* (scs-t-with-index *scs-t-f* *scs-t-pair*))
(assert-event (equal (fn-sco-records (fn-sco-thaw *scs-t-pair-f*)) *sco-t-events*))
(assert-event (equal (fn-cei-count *scs-t-pair*) 0))
(assert-event (not (fn-cei-correspondencep *scs-t-pair* *sco-t-events*)))
(assert-event (equal (fn-sco-thaw-checked *scs-t-pair-f*) (list :refused :index-shape)))
; The single sequence trie of the files written before a249a699 (the
; 20,000 fixture's): refused by the same test.
(defconst *scs-t-trie-f* (scs-t-with-index *scs-t-f* (car *scs-t-index*)))
(assert-event (equal (fn-sco-thaw-checked *scs-t-trie-f*) (list :refused :index-shape)))

; The named selection: witness, and fn-sco-select-named-is-select-unless-index-shape
; without its hypothesis (fn-sco-select calls :index-shape :corrupt).
(assert-event (equal (fn-sco-select-named :index-shape 0 2 4)
                     (list :full-replay :checkpoint-index-shape)))
(assert-event (equal (fn-sco-select-named :ok 1 2 4) (fn-sco-select :ok 1 2 4)))
(assert-event (equal (fn-sco-select-named :ok 1 2 4) (list :checkpoint 1)))
(assert-event (not (equal (fn-sco-select-named :index-shape 0 2 4)
                          (fn-sco-select :index-shape 0 2 4))))
(must-fail
 (defthm fn-scs-t-select-named-without-hypothesis
   (equal (fn-sco-select-named :index-shape 0 2 4)
          (fn-sco-select :index-shape 0 2 4))))
