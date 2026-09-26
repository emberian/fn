; Indexed Store sequence lookup has an exact committed-list authority.
(in-package "ACL2")
(include-book "../../books/consumer-event-index")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-ceit-events*
  (list '(:consumer 0 bootstrap) '(:consumer 1 register)
        '(:article 2 report) '(:consumer 3 ack)))
(defconst *fn-ceit-index* (fn-cei-build *fn-ceit-events*))
(assert-event (fn-cei-correspondencep *fn-ceit-index* *fn-ceit-events*))
(assert-event (equal (fn-cei-get 2 *fn-ceit-index*)
                     '(:article 2 report)))
(assert-event (equal (fn-cei-get 3 *fn-ceit-index*)
                     '(:consumer 3 ack)))
(assert-event (equal (fn-cei-get 4 *fn-ceit-index*) nil))

; A live completion extends one path and leaves the old root unchanged.
(defconst *fn-ceit-old* (fn-cei-build (take 3 *fn-ceit-events*)))
(defconst *fn-ceit-new*
  (fn-cei-put 3 '(:consumer 3 ack) *fn-ceit-old*))
(assert-event (equal *fn-ceit-new* *fn-ceit-index*))
(assert-event (equal (fn-cei-get 3 *fn-ceit-old*) nil))
(assert-event (equal (fn-cei-get 3 *fn-ceit-new*)
                     '(:consumer 3 ack)))

; The equality premise is necessary: a stale but well-shaped trie can still
; hold another event at the same sequence.  Neither the sequence field nor a
; matching group is enough to make it the Store's committed event.
(defconst *fn-ceit-corrupt*
  (fn-cei-put 2 '(:article 2 substituted) *fn-ceit-index*))
(assert-event (not (fn-cei-correspondencep
                    *fn-ceit-corrupt* *fn-ceit-events*)))
(must-fail
 (defthm fn-ceit-false-lookup-without-correspondence
   (equal (fn-cei-get 2 *fn-ceit-corrupt*)
          (nth 2 *fn-ceit-events*))))

; A lookup of an absent future sequence is not the last report.
(must-fail
 (defthm fn-ceit-false-future-lookup
   (equal (fn-cei-get 4 *fn-ceit-index*)
          (nth 3 *fn-ceit-events*))))

; PRF-180, the count: every put counts, so the built index of a history holds
; its length (fn-cei-count-of-build), and a live extension adds one.
(assert-event (equal (fn-cei-count *fn-ceit-index*) 4))
(assert-event (equal (fn-cei-count *fn-ceit-old*) 3))
(assert-event (equal (fn-cei-count *fn-ceit-new*) 4))
(assert-event (equal (fn-cei-count nil) 0))
; fn-cei-count-of-correspondence without its hypothesis: the corrupted index
; (a second put at sequence 2) does not correspond and counts 5 of 4 events.
(assert-event (not (fn-cei-correspondencep *fn-ceit-corrupt* *fn-ceit-events*)))
(assert-event (not (equal (fn-cei-count *fn-ceit-corrupt*)
                          (len *fn-ceit-events*))))
(must-fail
 (defthm fn-ceit-false-count-without-correspondence
   (equal (fn-cei-count index) (len events))))
