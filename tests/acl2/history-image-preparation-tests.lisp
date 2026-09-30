(in-package "ACL2")
(include-book "../../books/history-image-preparation")

; Source-only component fixture. This does not claim an installed source or
; native INITIAL authority; the real initializer must derive these fields.
(assert-event
 (mv-let (word start) (fn-hpip-begin 0 0 '(11 (3 0) 0 0)
                                    '(:maintenance 7 11 0) 7 17 19 23)
   (and (equal word :continue)
        (equal start
               '(:column 0 0 0 0 0 (11 (3 0) 0 0) (:maintenance 7 11 0) 7 17 19 23 nil)))))
(assert-event
 (mv-let (word start) (fn-hpip-begin 0 0 '(11 (3 0) 0 0)
                                    '(:maintenance 7 11 0) 7 17 19 23)
   (mv-let (word1 pool unused) (fn-hpip-tick start)
     (declare (ignore unused))
     (mv-let (word2 prepared writer) (fn-hpip-tick pool)
       (and (equal word :continue) (equal word1 :continue)
            (equal word2 :prepared) (equal (fn-omk-at 0 prepared) :prepared)
            (equal writer (fn-omk-at 12 prepared))
            (equal writer
                   (fn-hpi-begin 0 0 0 0 '(11 (3 0) 0 0)
                                 '(:maintenance 7 11 0) 7
                                 (fn-osj-native-offset-max) 17 19 23)))))))
; Three required column pages round to four using separate scheduling ticks.
(assert-event
 (mv-let (word start) (fn-hpip-begin 6144 0 '(11 (3 6144) 0 0)
                                    '(:maintenance 7 11 0) 7 17 19 23)
   (mv-let (word1 one unused1) (fn-hpip-tick start)
     (declare (ignore unused1))
     (mv-let (word2 two unused2) (fn-hpip-tick one)
       (declare (ignore unused2))
       (and (equal word :continue) (equal word1 :continue) (equal word2 :continue)
            (equal (fn-omk-at 0 one) :column)
            (equal (fn-omk-at 4 start) 1)
            (equal (fn-omk-at 4 one) 2)
            (equal (fn-omk-at 4 two) 4)
            (equal (fn-omk-at 5 two) 0))))))
; Three pool pages round independently after the column transition.
(assert-event
 (mv-let (word start) (fn-hpip-begin 1 49152 '(11 (3 1) 0 0)
                                    '(:maintenance 7 11 0) 7 17 19 23)
   (mv-let (word1 pool unused1) (fn-hpip-tick start)
     (declare (ignore unused1))
     (mv-let (word2 one unused2) (fn-hpip-tick pool)
       (declare (ignore unused2))
       (mv-let (word3 two unused3) (fn-hpip-tick one)
         (declare (ignore unused3))
         (mv-let (word4 prepared writer) (fn-hpip-tick two)
           (and (equal word :continue) (equal word1 :continue)
                (equal word2 :continue) (equal word3 :continue)
                (equal word4 :prepared) (equal (fn-omk-at 0 prepared) :prepared)
                (equal (fn-omk-at 5 pool) 1)
                (equal (fn-omk-at 4 pool) 1)
                (equal (fn-omk-at 4 one) 2)
                (equal (fn-omk-at 4 two) 4)
                (equal writer (fn-omk-at 12 prepared))
                (equal writer
                       (fn-hpi-begin 1 49152 1 4 '(11 (3 1) 0 0)
                                     '(:maintenance 7 11 0) 7
                                     (fn-osj-native-offset-max) 17 19 23)))))))))
(assert-event
 (mv-let (word next) (fn-hpip-begin 0 8 '(11 (3 0) 0 0)
                                   '(:maintenance 7 11 0) 7 17 19 23)
   (and (equal word :refused) (equal next nil))))
; A stale resource scalar refuses through the actual constructor, never a
; caller-provided success bit. The complete refused continuation is retained.
(assert-event
 (mv-let (word start) (fn-hpip-begin 0 0 '(11 (3 0) 0 0)
                                    '(:maintenance 7 12 0) 7 17 19 23)
   (mv-let (word1 pool unused) (fn-hpip-tick start)
     (declare (ignore unused))
     (mv-let (word2 refused writer) (fn-hpip-tick pool)
       (and (equal word :continue) (equal word1 :continue)
            (equal word2 :refused) (equal (fn-omk-at 0 refused) :refused)
            (equal writer (fn-omk-at 12 refused))
            (equal writer
                   (fn-hpi-begin 0 0 0 0 '(11 (3 0) 0 0)
                                 '(:maintenance 7 12 0) 7
                                 (fn-osj-native-offset-max) 17 19 23)))))))
