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

;; The offset the scan moves, as a proof-only mirror of its recursion; it is
;; never called by the host and appears only inside this book's lemmas.
(local
 (defun colp-offset (events group position frontier budget)
   (declare (xargs :measure (nfix budget)))
   (if (or (zp budget) (<= (nfix frontier) (nfix position)))
       0
     (if (not (consp events)) 0
       (let ((event (car events)))
         (cond
          ((or (not (fn-store-event-p event))
               (not (equal (fn-store-event-sequence event) position)))
           0)
          ((and (fn-stxa-p event) (not (fn-col-poll-article event))) 0)
          ((fn-col-matchp event group) 1)
          (t (1+ (colp-offset (cdr events) group (1+ position)
                              frontier (1- budget))))))))))

;; The event predicates stay closed: the lemmas are about the recursion.
(local
 (deftheory colp-closed
   '(fn-store-event-p fn-store-event-sequence fn-stxa-p fn-col-poll-article
     fn-record-p fn-record-groups fn-record-octets-string)))

(local
 (defthm colp-scan-position-is-offset
   (let ((scan (fn-col-poll-scan events group position frontier budget)))
     (implies (and (eq (car scan) :scan) (natp position))
              (equal (cadr scan)
                     (+ position (colp-offset events group position frontier budget)))))
   :hints (("Goal" :induct (colp-offset events group position frontier budget)
            :expand ((fn-col-poll-scan events group position frontier budget))
            :in-theory (e/d (fn-col-poll-scan) (colp-closed))))))

(local
 (defthm colp-offset-bounds
   (let ((k (colp-offset events group position frontier budget)))
     (and (natp k)
          (<= k (nfix budget))
          (implies (< 0 k) (< (nfix position) (nfix frontier)))
          (<= (+ (nfix position) k) (max (nfix position) (nfix frontier)))))
   :rule-classes nil
   :hints (("Goal" :induct (colp-offset events group position frontier budget)
            :in-theory (disable colp-closed)))))

(local
 (defthm colp-scan-event-is-offset-match
   (let ((scan (fn-col-poll-scan events group position frontier budget))
         (k (colp-offset events group position frontier budget)))
     (implies (and (eq (car scan) :scan) (natp position))
              (and (iff (caddr scan)
                        (and (< 0 k) (fn-col-matchp (nth (1- k) events) group)))
                   (implies (caddr scan)
                            (equal (caddr scan) (nth (1- k) events))))))
   :rule-classes nil
   :hints (("Goal" :induct (colp-offset events group position frontier budget)
            :expand ((fn-col-poll-scan events group position frontier budget))
            :in-theory (e/d (fn-col-poll-scan) (colp-closed))))))

(local (defthm colp-plus-cancel (equal (+ p (- p) x) (fix x))))
(local (defthm colp-plus-cancel-2 (equal (+ a p (- p) x) (+ a x))))

(local
 (defthm colp-offset-prefix-has-no-match
   (let ((k (colp-offset events group position frontier budget)))
     (and (implies (and (< 0 k) (fn-col-matchp (nth (1- k) events) group))
                   (fn-col-none-matchp (take (1- k) events) group))
          (implies (not (and (< 0 k) (fn-col-matchp (nth (1- k) events) group)))
                   (fn-col-none-matchp (take k events) group))))
   :rule-classes nil
   :hints (("Goal" :induct (colp-offset events group position frontier budget)
            :in-theory (disable colp-closed fn-col-matchp)))))

(local
 (defthm colp-empty-page-progresses
   (let ((scan (fn-col-poll-scan events group position frontier budget)))
     (implies (and (eq (car scan) :scan) (not (caddr scan)) (natp position)
                   (posp budget) (< position (nfix frontier)))
              (< 0 (colp-offset events group position frontier budget))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-col-poll-scan events group position frontier budget)
                            (colp-offset events group position frontier budget))
            :in-theory (disable colp-closed)))))

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
  :hints (("Goal" :use ((:instance colp-offset-bounds)
                        (:instance colp-scan-event-is-offset-match)
                        (:instance colp-offset-prefix-has-no-match)
                        (:instance colp-empty-page-progresses))
           :in-theory (disable fn-col-poll-scan colp-offset
                               fn-col-matchp fn-col-none-matchp colp-closed))))

; --- the host-called poll --------------------------------------------------

(local
 (defthm colp-scan-tag
   (implies (not (equal (car (fn-col-poll-scan events group position frontier budget))
                        :scan))
            (equal (car (fn-col-poll-scan events group position frontier budget))
                   :refused))
   :hints (("Goal" :induct (fn-col-poll-scan events group position frontier budget)
            :in-theory (e/d (fn-col-poll-scan) (colp-closed))))))

(local
 (defthm colp-scope-tag
   (implies (not (equal (car (fn-col-scope-entry s consumer)) :scope))
            (equal (car (fn-col-scope-entry s consumer)) :refused))
   :hints (("Goal" :in-theory (enable fn-col-scope-entry)))))

(local
 (defthm colp-scan-is-not-a-page
   (not (equal (car (fn-col-poll-scan events group position frontier budget))
               :poll))
   :hints (("Goal" :induct (fn-col-poll-scan events group position frontier budget)
            :in-theory (e/d (fn-col-poll-scan) (colp-closed colp-scan-tag))))))

(local
 (defthm colp-scope-is-not-a-page
   (not (equal (car (fn-col-scope-entry s consumer)) :poll))
   :hints (("Goal" :in-theory (enable fn-col-scope-entry)))))

; A page is a read: the host-called poll answers a page or a refusal, never
; a Store write proposal.
(defthm fn-col-poll-is-a-page-or-a-refusal
  (member-equal (car (fn-col-poll o consumer)) '(:poll :refused))
  :hints (("Goal" :in-theory (e/d (fn-col-poll)
                                  (fn-col-poll-scan fn-col-scope-entry
                                   fn-col-poll-index-window fn-cp-cursor-encode
                                   fn-cp-scope-cursor colp-closed)))))

(defthm fn-col-poll-is-the-index-window-scan-unfolds
  (implies (equal (car (fn-col-poll o consumer)) :poll)
           (let* ((store (fn-own-store o))
                  (s (fn-sn-consumer store))
                  (scoped (fn-col-scope-entry s consumer))
                  (entry (fn-cp-nth 1 scoped))
                  (position (fn-cp-nth 7 entry))
                  (frontier (fn-cp-nth 3 s))
                  (scan (fn-col-poll-scan
                         (fn-col-poll-index-window
                          (fn-sn-event-index store) position frontier
                          *fn-col-poll-max-scan*)
                         (fn-cp-nth 3 entry) position frontier
                         *fn-col-poll-max-scan*)))
             (and (equal (car scoped) :scope)
                  (equal (car scan) :scan)
                  (equal (fn-col-poll o consumer)
                         (list :poll
                               (fn-cp-cursor-encode
                                (update-nth 9 (fn-cp-nth 1 scan)
                                            (fn-cp-scope-cursor s entry)))
                               (fn-cp-nth 2 scan))))))
  :hints (("Goal" :in-theory (e/d (fn-col-poll)
                                  (fn-col-poll-scan fn-col-scope-entry
                                   fn-col-poll-index-window fn-cp-cursor-encode
                                   fn-cp-scope-cursor update-nth fn-cp-nth
                                   colp-closed)))))

; The scoped entry's recorded position is a natural, the page contract's
; remaining hypothesis.
(defthm fn-col-scope-entry-position-is-natural
  (implies (equal (car (fn-col-scope-entry s consumer)) :scope)
           (natp (fn-cp-nth 7 (fn-cp-nth 1 (fn-col-scope-entry s consumer)))))
  :hints (("Goal" :in-theory (enable fn-col-scope-entry))))

; --- the host-called ack ---------------------------------------------------

(defthm fn-col-ack-is-the-kernel-ack-unfolds
  (implies (and (equal (fn-cp-nth 0 (fn-cp-cursor-decode bytes)) :ok)
                (fn-sn-consumer (fn-own-store o)))
           (equal (fn-col-ack o bytes)
                  (fn-col-result-event
                   o (fn-cp-ack (fn-sn-consumer (fn-own-store o))
                                *fn-col-principal* *fn-col-query-version*
                                *fn-col-view-version*
                                (fn-cp-nth 1 (fn-cp-cursor-decode bytes))))))
  :hints (("Goal" :in-theory (e/d (fn-col-ack)
                                  (fn-cp-cursor-decode fn-col-result-event
                                   fn-cp-ack fn-cp-nth)))))

(defthm fn-cp-ack-writes-only-a-forward-declaration-in-scope
  (let ((result (fn-cp-ack s caller qver view cursor))
        (entry (fn-cp-find (fn-cp-nth 3 cursor) (fn-cp-nth 5 s))))
    (and (implies (equal (car result) :write)
                  (and (equal (cadr result) (list :ack cursor))
                       (fn-cp-scope-matchp s caller qver view cursor entry)
                       (<= (nfix (fn-cp-nth 7 entry)) (fn-cp-nth 9 cursor))
                       (not (equal (fn-cp-nth 9 cursor) (fn-cp-nth 7 entry)))
                       (<= (fn-cp-nth 9 cursor) (nfix (fn-cp-nth 3 s)))))
         (implies (and (fn-cp-scope-matchp s caller qver view cursor entry)
                       (equal (fn-cp-nth 9 cursor) (fn-cp-nth 7 entry))
                       (<= (fn-cp-nth 9 cursor) (nfix (fn-cp-nth 3 s))))
                  (equal result (list :no-op (fn-cp-scope-cursor s entry))))))
  :hints (("Goal" :in-theory (enable fn-cp-ack))))

(local (defthm colp-cp-nth-of-cons-zero (equal (fn-cp-nth 0 (cons a b)) a)
         :hints (("Goal" :expand ((fn-cp-nth 0 (cons a b)))))))
(local (defthm colp-cp-nth-of-cons
         (implies (posp n) (equal (fn-cp-nth n (cons a b)) (fn-cp-nth (1- n) b)))
         :hints (("Goal" :expand ((fn-cp-nth n (cons a b)))))))
(local (defthm colp-cp-find-of-cons-own
         (implies (equal (fn-cp-nth 1 e) c)
                  (equal (fn-cp-find c (cons e rest)) e))
         :hints (("Goal" :expand ((fn-cp-find c (cons e rest)))))))

(defthm fn-cp-ack-after-its-commit-is-a-no-op
  (implies (equal (car (fn-cp-ack s caller qver view cursor)) :write)
           (equal (car (fn-cp-ack (fn-cp-apply s (list :ack cursor))
                                  caller qver view cursor))
                  :no-op))
  :hints (("Goal" :in-theory (e/d (fn-cp-ack fn-cp-apply fn-cp-scope-matchp
                                   fn-cp-entry fn-cp-state)
                                  (fn-cp-cursorp fn-cp-remove)))))
