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
(defun fn-col-poll-article (event)
  (if (fn-stxa-p event) (fn-replay-composite-record event)
    (if (fn-record-p event) event nil)))
(verify-guards fn-col-poll-article)

(defun fn-col-poll-event-decision (event group position)
  (declare (xargs :guard t))
  (let ((article (fn-col-poll-article event)))
    (cond
     ((or (not (fn-store-event-p event))
          (not (equal (fn-store-event-sequence event) position)))
      :history)
     ((and (fn-stxa-p event) (not article)) :article-binding)
     ((and (fn-record-p article)
           (true-listp (fn-record-groups article))
           (member-equal (fn-record-octets-string group)
                         (fn-record-groups article)))
      :match)
     (t :skip))))
(verify-guards fn-col-poll-event-decision)
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
             (decision (fn-col-poll-event-decision event group position)))
        (case decision
         (:history (list :refused :history))
         (:article-binding (list :refused :article-binding))
         (:match (list :scan (1+ position) event))
         (otherwise (fn-col-poll-scan (cdr events) group (1+ position)
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
                (natp position) (natp frontier) (natp budget)
                (<= frontier (len events)))
           (equal (fn-col-poll-index-window index position frontier budget)
                  (fn-col-poll-list-window events position frontier budget)))
  :hints (("Goal" :induct (fn-col-poll-index-window
                            index position frontier budget)
           :in-theory (disable fn-cei-correspondencep fn-cei-build
                               fn-cei-build-aux fn-cei-get))))
