; Generic history exports: alternate concrete attachment precedes this book.
(in-package "ACL2")
(include-book "history-columns-foundation")

(defabsstobj fn-hist
  :attachable t
  :foundation fn-hist$c
  :recognizer (fn-hist-p :logic fn-hist$ap :exec fn-hist$cp)
  :creator (create-fn-hist :logic create-fn-hist$a :exec create-fn-hist$c)
  :corr-fn fn-hist$corr
  :exports ((fn-hist-count :logic fn-hist$a-count :exec fn-hist$c-count)
            (fn-hist-at :logic fn-hist$a-at :exec fn-hist$c-at)
            (fn-hist-msgid-records :logic fn-hist$a-msgid-records
                                   :exec fn-hist$c-msgid-records)
            (fn-hist-append :logic fn-hist$a-append :exec fn-hist$c-append
                            :protect t)
            (fn-hist-clear :logic fn-hist$a-clear :exec fn-hist$c-clear
                           :protect t))
  :corr-fn-exists t)

; -----------------------------------------------------------------------------
; The logical view, opened: a theorem over `fn-hist' is a theorem over the
; history list.

(defthm fn-hist-p-is-true-listp
  (equal (fn-hist-p x) (true-listp x)))

(defthm fn-hist-count-is-len
  (equal (fn-hist-count fn-hist) (len fn-hist)))

(defthm fn-hist-at-is-nth
  (equal (fn-hist-at seq fn-hist) (nth seq fn-hist)))

(defthm fn-hist-msgid-records-is-records-for
  (equal (fn-hist-msgid-records msgid fn-hist)
         (fn-cei-article-records-for msgid fn-hist)))

(defthm fn-hist-append-is-append
  (equal (fn-hist-append ev fn-hist) (append fn-hist (list ev))))

(defthm fn-hist-clear-is-nil
  (equal (fn-hist-clear salt fn-hist) nil))

(in-theory (disable fn-hist-p fn-hist-count fn-hist-at fn-hist-msgid-records
                    fn-hist-append fn-hist-clear))

; -----------------------------------------------------------------------------
; The open: the history loaded into a cleared stobj, one append per event.
; What stage 2's host entries call where the store node builds its index
; today (`fn-cei-build' at every open).

(defun fn-hist-load-events (events fn-hist)
  (declare (xargs :stobjs fn-hist :guard (true-listp events)))
  (if (consp events)
      (let ((fn-hist (fn-hist-append (car events) fn-hist)))
        (fn-hist-load-events (cdr events) fn-hist))
    fn-hist))

(defun fn-hist-load (events salt fn-hist)
  (declare (xargs :stobjs fn-hist
                  :guard (and (true-listp events) (unsigned-byte-p 32 salt))))
  (let ((fn-hist (fn-hist-clear salt fn-hist)))
    (fn-hist-load-events events fn-hist)))

(defthm fn-hist-load-events-is-append
  (implies (true-listp fn-hist)
           (equal (fn-hist-load-events events fn-hist)
                  (append fn-hist (true-list-fix events)))))

; KEYSTONE (the open establishes the relation): the stobj the load answers
; IS the history, for every salt; so every later `fn-hist-append' of the
; event the store commits keeps it the history (`fn-hist-append-is-append').
(defthm fn-hist-load-is-the-history
  (implies (true-listp events)
           (equal (fn-hist-load events salt fn-hist) events)))

(in-theory (disable fn-hist-load fn-hist-load-events))

; -----------------------------------------------------------------------------
; The store node's event index, served from the history (PKT-PRS-1's
; event-index half, PKT-PRS-4).  Under the correspondence the store carries
; for its index (`fn-cei-correspondencep', books/consumer-event-index.lisp;
; established at every open and preserved by every transition,
; books/history-columns-relation.lisp (the retired index's invariants were deleted)), each of the index's
; three answers is the stobj's answer over the same history: the count, the
; event at a sequence (one array read; the radix trie's path of four
; octets is not needed), and the article records under a Message-ID (the
; salted bucket, compared exactly).  So a reader of the index reads the
; stobj instead, and the index has nothing left to hold.

(defthm fn-hist-count-serves-cei-count
  (implies (fn-cei-correspondencep index fn-hist)
           (equal (fn-cei-count index) (fn-hist-count fn-hist))))

(local
 (defthm fn-hist-nth-true-list-fix
   (equal (nth n (true-list-fix x)) (nth n x))))

(local
 (defthm fn-hist-len-true-list-fix
   (equal (len (true-list-fix x)) (len x))))

(local
 (defthm fn-hist-nth-past-len
   (implies (and (natp n) (<= (len x) n)) (equal (nth n x) nil))
   :hints (("Goal" :induct (nth n x)
            :in-theory (union-theories '(nth len nfix natp zp car-cons cdr-cons)
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-hist-cei-build-aux-true-list-fix
   (equal (fn-cei-build-aux (true-list-fix events) sequence index)
          (fn-cei-build-aux events sequence index))
   :hints (("Goal" :in-theory (disable fn-cei-put)))))

; The event at every natural sequence: inside the history the event, past
; it nil from both (so no bound on SEQ against the count is needed); the
; history within the index's uint32 key space.
(defthm fn-hist-at-serves-cei-get
  (implies (and (fn-cei-correspondencep index fn-hist)
                (<= (len fn-hist) (1+ *fn-cbor-max-uint*))
                (natp seq))
           (equal (fn-cei-get seq index) (fn-hist-at seq fn-hist)))
  :hints (("Goal" :cases ((fn-cp-uintp seq))
           :use ((:instance fn-cei-get-of-build-is-committed-event
                            (events (true-list-fix fn-hist)) (sequence seq)))
           :in-theory (e/d (fn-cei-correspondencep fn-cei-build)
                           (fn-cei-get-of-build-is-committed-event fn-cei-get
                            fn-cei-build-aux nth true-list-fix len)))
          ("Subgoal 2" :in-theory (e/d (fn-cp-uintp fn-cei-get) (nth len)))))

(local
 (defthm fn-hist-held-msgid-stringp
   (implies (fn-held-p x) (stringp (fn-record-msgid x)))
   :hints (("Goal" :in-theory (enable fn-held-p fn-held-internals fn-record-internals
                                      fn-record-msgidp)))))

(local
 (defthm fn-hist-records-for-non-string
   (implies (not (stringp m))
            (equal (fn-cei-article-records-for m events) nil))
   :hints (("Goal" :in-theory (disable fn-held-p fn-cei-event-article)))))

(local
 (defthm fn-hist-msgid-records-serve-cei-string
   (implies (and (fn-cei-correspondencep index fn-hist)
                 (stringp msgid))
            (equal (fn-cei-msgid-records msgid index)
                   (fn-hist-msgid-records msgid fn-hist)))
   :hints (("Goal" :in-theory (disable fn-cei-msgid-records
                                       fn-cei-correspondencep)))))

; The article records under every Message-ID (a non-string names none in
; either).
(defthm fn-hist-msgid-records-serve-cei
  (implies (fn-cei-correspondencep index fn-hist)
           (equal (fn-cei-msgid-records msgid index)
                  (fn-hist-msgid-records msgid fn-hist)))
  :hints (("Goal" :cases ((stringp msgid))
           :in-theory (disable fn-cei-correspondencep fn-cei-msgid-records))
          ("Subgoal 2" :in-theory (enable fn-cei-msgid-records fn-cei-trie-records))))
