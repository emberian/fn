; E2 Store-journal event codec witnesses.  Publication and replay are separate.
(in-package "ACL2")
(include-book "../../books/consumer-store-events")
(include-book "std/testing/must-fail" :dir :system)

(defconst *cpet-cursor*
  (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 2 3 4))
(defconst *cpet-events*
  (list (fn-cpe-make 0 2 1 '(:bootstrap (1) (2)))
        (fn-cpe-make 1 3 1 '(:register (3) (4) (5) 1 2 3))
        (fn-cpe-make 2 4 1 (list :ack *cpet-cursor*))
        (fn-cpe-make 3 5 1 '(:rebase (3) (4) (5) 1 3 4))
        (fn-cpe-make 4 6 1 '(:unregister (3) 4))
        (fn-cpe-make 5 7 1 '(:rollover (9)))))

(defun cpet-roundtripp (events)
  (if (endp events) t
    (and (fn-cpe-eventp (car events))
         (equal (fn-cpe-decode-exact (fn-cpe-encode (car events)))
                (list :ok (car events)))
         (cpet-roundtripp (cdr events)))))

(assert-event (cpet-roundtripp *cpet-events*))
(assert-event (equal (len (fn-cpe-encode (nth 2 *cpet-events*)))
                     (+ 18 (len (fn-cp-cursor-encode *cpet-cursor*)))))
(defconst *cpet-max-id* (make-list 64 :initial-element 255))
(defconst *cpet-max-cursor*
  (fn-cp-cursor *cpet-max-id* *cpet-max-id* *cpet-max-id*
                *cpet-max-id* *cpet-max-id* 4294967295 4294967295
                4294967295 4294967295))
(assert-event (equal (len (fn-cpe-encode
                           (fn-cpe-make 0 0 0 (list :ack *cpet-max-cursor*))))
                     364))
(assert-event (equal (fn-cpe-decode-exact
                      (append (fn-cpe-encode (car *cpet-events*)) '(0)))
                     '(:error :operation)))
(assert-event (equal (fn-cpe-decode-exact (make-list 513 :initial-element 0))
                     '(:error :octets)))
(assert-event (equal (fn-cpe-decode-exact
                      (cons 0 (cdr (fn-cpe-encode (car *cpet-events*)))))
                     '(:error :version)))
(must-fail (defthm cpet-roundtrip-needs-valid-event
             (equal (fn-cpe-decode-exact (fn-cpe-encode event))
                    (list :ok event))))
