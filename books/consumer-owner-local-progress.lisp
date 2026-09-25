; fn: what the local owner's consumer poll and ack do to a consumer's position
; (CNS-002, PRF-116).
;
; The host calls `fn-col-poll' and `fn-col-ack' (host/owner-host.lisp
; fn-owner-consumer-local-poll / -ack, reached from the native control
; handler host/native/owner.lisp fnn-owner-consumer-local-serialized).  An
; E2 position is a committed Store-event prefix, not a per-group number.
;
; 1. A page is a read.  Poll never proposes a Store write; only ack does.
; 2. The selector's page contract, over any event window: the continuation
;    lies in [position, min(frontier, position+budget)]; an empty page
;    scanned only non-matching events and, when anything was scannable,
;    moved past at least one of them; a nonempty page is the first matching
;    event of its window, at the position just before the continuation.  So
;    a continuation never passes a matching event it did not return.
; 3. `fn-col-poll' is that selector over the carried index window, with the
;    continuation written into the owner-pinned scope cursor.
; 4. Ack writes exactly the declared cursor, only forward, only within the
;    committed frontier, only in the recorded scope; an equal position is an
;    idempotent no-op, and after the committed ack the same ack is a no-op.
(in-package "ACL2")
(include-book "consumer-owner-local")

; --- the page contract of the selector ------------------------------------

(defun fn-col-matchp (event group)
  "The poll's selection test: a group-matching accepted article event."
  (let ((article (fn-col-poll-article event)))
    (and (fn-record-p article)
         (true-listp (fn-record-groups article))
         (member-equal (fn-record-octets-string group)
                       (fn-record-groups article))
         t)))

(defun fn-col-none-matchp (events group)
  (if (consp events)
      (and (not (fn-col-matchp (car events) group))
           (fn-col-none-matchp (cdr events) group))
    t))

(defthm fn-col-poll-scan-page-contract
  (let ((scan (fn-col-poll-scan events group position frontier budget)))
    (implies (and (eq (car scan) :scan) (natp position))
             (let ((p (cadr scan)) (event (caddr scan)))
               (and (natp p)
                    (<= position p)
                    (<= p (max position (nfix frontier)))
                    (<= p (+ position (nfix budget)))
                    (if event
                        (and (< position p)
                             (equal event (nth (- p (+ 1 position)) events))
                             (fn-col-matchp event group)
                             (fn-col-none-matchp (take (- p (+ 1 position)) events)
                                                 group))
                      (and (fn-col-none-matchp (take (- p position) events) group)
                           (implies (and (posp budget) (< position (nfix frontier)))
                                    (< position p))))))))
  :hints (("Goal" :induct (fn-col-poll-scan events group position frontier budget)
           :in-theory (enable fn-col-poll-scan))))

; --- the host-called poll --------------------------------------------------

(defthm fn-col-poll-proposes-no-write-by-definition
  (not (equal (car (fn-col-poll o consumer)) :write)))

(defthm fn-col-poll-is-the-index-window-scan-unfolds
  (implies (equal (car (fn-col-poll o consumer)) :poll)
           (let* ((store (fn-own-store o))
                  (s (fn-sn-consumer store))
                  (entry (cadr (fn-col-scope-entry s consumer)))
                  (position (fn-cp-nth 7 entry))
                  (frontier (fn-cp-nth 3 s))
                  (scan (fn-col-poll-scan
                         (fn-col-poll-index-window
                          (fn-sn-event-index store) position frontier
                          *fn-col-poll-max-scan*)
                         (fn-cp-nth 3 entry) position frontier
                         *fn-col-poll-max-scan*)))
             (and (equal (car (fn-col-scope-entry s consumer)) :scope)
                  (natp position)
                  (equal (car scan) :scan)
                  (equal (fn-col-poll o consumer)
                         (list :poll
                               (fn-cp-cursor-encode
                                (update-nth 9 (cadr scan)
                                            (fn-cp-scope-cursor s entry)))
                               (caddr scan))))))
  :hints (("Goal" :in-theory (enable fn-col-poll fn-col-scope-entry fn-cp-nth))))

; --- the host-called ack ---------------------------------------------------

(defthm fn-col-ack-is-the-kernel-ack-unfolds
  (implies (not (equal (car (fn-col-ack o bytes)) :refused))
           (let ((decoded (fn-cp-cursor-decode bytes))
                 (s (fn-sn-consumer (fn-own-store o))))
             (and (equal (fn-cp-nth 0 decoded) :ok)
                  s
                  (equal (fn-col-ack o bytes)
                         (fn-col-result-event
                          o (fn-cp-ack s *fn-col-principal* *fn-col-query-version*
                                       *fn-col-view-version* (fn-cp-nth 1 decoded)))))))
  :hints (("Goal" :in-theory (enable fn-col-ack fn-cp-cursor-decode))))

(defthm fn-cp-ack-writes-only-a-forward-declaration-in-scope
  (let ((result (fn-cp-ack s caller qver view cursor))
        (entry (fn-cp-find (fn-cp-nth 3 cursor) (fn-cp-nth 5 s))))
    (and (implies (equal (car result) :write)
                  (and (equal (cadr result) (list :ack cursor))
                       (fn-cp-scope-matchp s caller qver view cursor entry)
                       (< (nfix (fn-cp-nth 7 entry)) (fn-cp-nth 9 cursor))
                       (<= (fn-cp-nth 9 cursor) (nfix (fn-cp-nth 3 s)))))
         (implies (and (fn-cp-scope-matchp s caller qver view cursor entry)
                       (equal (fn-cp-nth 9 cursor) (fn-cp-nth 7 entry)))
                  (equal result (list :no-op (fn-cp-scope-cursor s entry))))))
  :hints (("Goal" :in-theory (enable fn-cp-ack))))

(defthm fn-cp-ack-after-its-commit-is-a-no-op
  (implies (equal (car (fn-cp-ack s caller qver view cursor)) :write)
           (equal (car (fn-cp-ack (fn-cp-apply s (list :ack cursor))
                                  caller qver view cursor))
                  :no-op))
  :hints (("Goal" :in-theory (enable fn-cp-ack fn-cp-apply))))
