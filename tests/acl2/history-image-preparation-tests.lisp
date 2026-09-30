(in-package "ACL2")
(include-book "../../books/history-image-preparation")

; Source-only component fixture. This does not claim an installed source or
; native INITIAL authority; the real initializer must derive these fields.
(assert-event
 (equal (mv-nth 1 (fn-hpip-begin 0 0 '(11 (3 0) 0 0)
                                 '(:maintenance 7 11 0) 7 17 19 23))
        '(:column 0 0 0 0 0 (11 (3 0) 0 0) (:maintenance 7 11 0) 7 17 19 23 nil)))
(assert-event
 (let* ((start (mv-nth 1 (fn-hpip-begin 0 0 '(11 (3 0) 0 0)
                                     '(:maintenance 7 11 0) 7 17 19 23)))
        (pool (mv-nth 1 (fn-hpip-tick start))))
   (and (equal (mv-nth 0 (fn-hpip-tick pool)) :prepared)
        (equal (mv-nth 2 (fn-hpip-tick pool))
               (fn-hpi-begin 0 0 0 0 '(11 (3 0) 0 0)
                             '(:maintenance 7 11 0) 7
                             (fn-osj-native-offset-max) 17 19 23)))))
; Three required column pages round to four using separate scheduling ticks.
(assert-event
 (let* ((start (mv-nth 1 (fn-hpip-begin 6144 0 '(11 (3 6144) 0 0)
                                     '(:maintenance 7 11 0) 7 17 19 23)))
        (one (mv-nth 1 (fn-hpip-tick start)))
        (two (mv-nth 1 (fn-hpip-tick one))))
   (and (equal (fn-omk-at 0 one) :column)
        (equal (fn-omk-at 4 start) 1)
        (equal (fn-omk-at 4 one) 2)
        (equal (fn-omk-at 4 two) 4)
        (equal (fn-omk-at 5 two) 0))))
; Three pool pages round independently after the column transition.
(assert-event
 (let* ((start (mv-nth 1 (fn-hpip-begin 1 49152 '(11 (3 1) 0 0)
                                     '(:maintenance 7 11 0) 7 17 19 23)))
        (pool (mv-nth 1 (fn-hpip-tick start)))
        (one (mv-nth 1 (fn-hpip-tick pool)))
        (two (mv-nth 1 (fn-hpip-tick one))))
   (and (equal (fn-omk-at 5 pool) 1)
        (equal (fn-omk-at 4 pool) 1)
        (equal (fn-omk-at 4 one) 2)
        (equal (fn-omk-at 4 two) 4)
        (equal (mv-nth 0 (fn-hpip-tick two)) :prepared)
        (equal (mv-nth 2 (fn-hpip-tick two))
               (fn-hpi-begin 1 49152 1 4 '(11 (3 1) 0 0)
                             '(:maintenance 7 11 0) 7
                             (fn-osj-native-offset-max) 17 19 23)))))
(assert-event
 (equal (mv-nth 0 (fn-hpip-begin 0 8 '(11 (3 0) 0 0)
                               '(:maintenance 7 11 0) 7 17 19 23)) :refused))
; A stale resource scalar refuses through the actual constructor, never a
; caller-provided success bit. The complete refused continuation is retained.
(assert-event
 (let* ((start (mv-nth 1 (fn-hpip-begin 0 0 '(11 (3 0) 0 0)
                                     '(:maintenance 7 12 0) 7 17 19 23)))
        (pool (mv-nth 1 (fn-hpip-tick start))))
   (and (equal (mv-nth 0 (fn-hpip-tick pool)) :refused)
        (equal (mv-nth 2 (fn-hpip-tick pool))
               (fn-hpi-begin 0 0 0 0 '(11 (3 0) 0 0)
                             '(:maintenance 7 12 0) 7
                             (fn-osj-native-offset-max) 17 19 23)))))
