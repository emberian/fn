; Bounded Store event selection shared by the actual owner poll.
(in-package "ACL2")
(include-book "replay")
(include-book "consumer-event-index")

; A poll inspects at most sixteen consecutive committed Store events and
; stops at its first group-matching accepted article.  Its cursor names the
; last inspected prefix, never an omitted matching article.  The selected
; event is handed unchanged to the ACL2 owner wrapper for exact encoding:
; schema-1 stxa includes the received article, bound exact
; authored source and historical verdict; legacy events remain explicitly
; distinguishable by their own versioned bytes.  Poll has no Store write.
(defconst *fn-col-poll-max-scan* 16)
; The article record a history event commits.  After the records flip the
; history retains an accepted statement as the composite ROW (`fn-hstxa-p')
; and a plain article as a HELD row (`fn-held-p', books/held-record.lisp): the
; row's interned article is its article, as the wire composite's decoded
; record was; the wire vocabulary (a composite or record handed over before
; the intern) reads as before.  The selected event is still the event
; itself; its report reads its bytes through the arena
; (books/consumer-owner-local.lisp fn-col-poll-report-over).
(defun fn-col-poll-article (event)
  (cond ((fn-hstxa-p event) (fn-hstxa-held event))
        ((fn-stxa-p event) (fn-replay-composite-record event))
        ((fn-held-p event) event)
        ((fn-record-p event) event)
        (t nil)))
(verify-guards fn-col-poll-article)
; An article record in either vocabulary, and a composite in either: one
; test each, so a proof over the scan splits as it did before the flip.
(defun fn-col-poll-articlep (article)
  (declare (xargs :guard t))
  (or (fn-held-p article) (fn-record-p article)))
(defun fn-col-poll-compositep (event)
  (declare (xargs :guard t))
  (or (fn-hstxa-p event) (fn-stxa-p event)))
(defun fn-col-poll-window (events budget)
  (declare (xargs :guard (natp budget) :measure (nfix budget)))
  (if (and (posp budget) (consp events))
      (cons (car events) (fn-col-poll-window (cdr events) (1- budget)))
    nil))
(verify-guards fn-col-poll-window)
(defthm fn-col-poll-window-is-true-list
  (true-listp (fn-col-poll-window events budget))
  :hints (("Goal" :induct (fn-col-poll-window events budget)
           :in-theory (enable fn-col-poll-window))))
(defun fn-col-poll-drop (events count)
  (declare (xargs :guard (natp count) :measure (nfix count)))
  (if (zp count) events
    (fn-col-poll-drop (if (consp events) (cdr events) nil)
                      (1- count))))
(verify-guards fn-col-poll-drop)
(defun fn-col-poll-scan (events group position frontier budget)
  (declare (xargs :guard (and (true-listp events) (fn-cp-idp group)
                              (natp position) (natp frontier) (natp budget))
                  :measure (nfix budget)))
  (if (or (zp budget) (<= (nfix frontier) (nfix position)))
      (list :scan position nil)
    (if (not (consp events)) (list :refused :history)
      (let* ((event (car events))
             (article (fn-col-poll-article event)))
        (cond
         ((or (not (fn-store-event-p event))
              (not (equal (fn-store-event-sequence event) position)))
          (list :refused :history))
         ((and (fn-col-poll-compositep event) (not article))
          (list :refused :article-binding))
         ((and (fn-col-poll-articlep article)
               (true-listp (fn-record-groups article))
               (member-equal (fn-record-octets-string group)
                             (fn-record-groups article)))
          (list :scan (1+ position) event))
         (t (fn-col-poll-scan (cdr events) group (1+ position)
                              frontier (1- budget))))))))
(verify-guards fn-col-poll-scan)

; The Store carries this rebuildable index from the exact committed journal.
; Materialize only the bounded scan window, then use the original article
; selector.  No acknowledged-prefix walk occurs on the served path.
(defun fn-col-poll-index-window (index position frontier budget)
  (declare (xargs :guard (and (natp position) (natp frontier) (natp budget))
                  :measure (nfix budget)))
  (if (or (zp budget) (<= (nfix frontier) (nfix position)))
      nil
    (cons (fn-cei-get position index)
          (fn-col-poll-index-window index (1+ position) frontier
                                    (1- budget)))))
(verify-guards fn-col-poll-index-window)

(defthm fn-col-poll-index-window-length-bound
  (implies (natp budget)
           (<= (len (fn-col-poll-index-window
                     index position frontier budget))
               budget))
  :hints (("Goal" :induct (fn-col-poll-index-window
                            index position frontier budget))))

(defthm fn-col-poll-drop-one
  (implies (natp position)
           (equal (fn-col-poll-drop events (1+ position))
                  (if (consp (fn-col-poll-drop events position))
                      (cdr (fn-col-poll-drop events position))
                    nil)))
  :hints (("Goal" :induct (fn-col-poll-drop events position)
           :in-theory (enable fn-col-poll-drop))))

(defthm fn-col-poll-drop-head-is-nth
  (implies (natp position)
           (equal (car (fn-col-poll-drop events position))
                  (nth position events)))
  :hints (("Goal" :induct (fn-col-poll-drop events position)
           :in-theory (enable fn-col-poll-drop nth))))

(defthm fn-col-poll-position-is-u32
  (implies (and (natp position) (< position frontier)
                (<= frontier (1+ *fn-cbor-max-uint*)))
           (fn-cp-uintp position))
  :hints (("Goal" :in-theory (enable fn-cp-uintp))))

(defthm fn-col-poll-index-lookup-is-drop-head
  (implies (and (fn-cei-correspondencep index events)
                (true-listp events)
                (<= (len events) (1+ *fn-cbor-max-uint*))
                (natp position) (< position (len events)))
           (equal (fn-cei-get position index)
                  (car (fn-col-poll-drop events position))))
  :hints (("Goal" :use ((:instance fn-cei-correspondence-lookup
                                    (sequence position)))
           :in-theory (disable fn-cei-correspondencep fn-cei-build
                               fn-cei-build-aux fn-cei-get))))

(defthm fn-col-poll-index-get-non-uint-is-nil-by-definition
  (implies (not (fn-cp-uintp position))
           (equal (fn-cei-get position index) nil))
  :hints (("Goal" :in-theory (enable fn-cei-get))))

(defthm fn-col-poll-index-get-past-end-is-nil
  (implies (and (fn-cei-correspondencep index events)
                (true-listp events)
                (<= (len events) (1+ *fn-cbor-max-uint*))
                (natp position)
                (<= (len events) position))
           (equal (fn-cei-get position index) nil))
  :hints (("Goal"
           :cases ((fn-cp-uintp position))
           :use ((:instance fn-cei-get-of-build-is-committed-event
                            (sequence position)))
           :in-theory (e/d (fn-cei-correspondencep)
                           (fn-cei-build fn-cei-build-aux fn-cei-get
                            fn-cei-get-of-build-is-committed-event)))))

(defthm fn-col-poll-nth-past-end-is-nil
  (implies (and (natp position) (<= (len events) position))
           (equal (nth position events) nil))
  :hints (("Goal" :induct (fn-col-poll-drop events position)
           :in-theory (enable nth len fn-col-poll-drop))))

(defthm fn-col-poll-index-lookup-is-drop-head-total
  (implies (and (fn-cei-correspondencep index events)
                (true-listp events)
                (<= (len events) (1+ *fn-cbor-max-uint*))
                (natp position))
           (equal (fn-cei-get position index)
                  (car (fn-col-poll-drop events position))))
  :hints (("Goal"
           :cases ((< position (len events)))
           :use ((:instance fn-col-poll-index-lookup-is-drop-head)
                 (:instance fn-col-poll-index-get-past-end-is-nil))
           :do-not-induct t
           :in-theory (e/d (fn-col-poll-drop-head-is-nth)
                           (fn-cei-correspondencep fn-cei-build fn-cei-get
                            fn-cei-build-aux
                            fn-col-poll-index-lookup-is-drop-head
                            fn-col-poll-index-get-past-end-is-nil)))))

; This proof notation uses the old list suffix.  It is never called by poll.
(defun fn-col-poll-list-window (events position frontier budget)
  (declare (xargs :guard (and (natp position) (natp frontier) (natp budget))
                  :measure (nfix budget) :verify-guards nil))
  (if (or (zp budget) (<= (nfix frontier) (nfix position)))
      nil
    (cons (car (fn-col-poll-drop events position))
          (fn-col-poll-list-window events (1+ position) frontier
                                   (1- budget)))))

; Every event handed to the unchanged group/article selector is the exact
; committed Store event at its dense sequence, including any unknown kind
; that the selector explicitly refuses.
(defthm fn-col-poll-index-window-is-committed-prefix
  (implies (and (fn-cei-correspondencep index events)
                (true-listp events)
                (<= (len events) (1+ *fn-cbor-max-uint*))
                (natp position) (natp frontier) (natp budget))
           (equal (fn-col-poll-index-window index position frontier budget)
                  (fn-col-poll-list-window events position frontier budget)))
  :hints (("Goal" :induct (fn-col-poll-index-window
                            index position frontier budget)
           :in-theory (disable fn-cei-correspondencep fn-cei-build
                               fn-cei-build-aux fn-cei-get))))
