(in-package "ACL2")
(include-book "../books/startup-groups")

(assert-event
 (let ((profile '((:groups ("default" . 1)) (:other . 17))))
  (and (equal (fn2-startup-groups-from-text profile nil) profile)
       (equal (fn2-startup-groups-from-text profile "")
              '((:groups) (:other . 17)))
       (equal (fn2-startup-groups-from-text profile
                (coerce '(#\, #\Space #\Newline #\Tab #\Return #\,) 'string))
              '((:groups) (:other . 17))))))

(assert-event
 (equal
  (fn2-startup-groups-from-text
   '((:other . 17))
   (concatenate 'string
    ", b.test " (coerce '(#\Return #\Newline #\Tab) 'string)
    "a x.test,," (coerce '(#\Newline #\Space) 'string)
    "b.test," (coerce '(#\Tab) 'string) "c.test" (coerce '(#\Return) 'string)))
  '((:other . 17) (:groups ("b.test" . 1) ("a x.test" . 2)
                          ("b.test" . 3) ("c.test" . 4)))))

; Only space, tab and carriage return trim. Internal whitespace and other
; characters survive parsing, to be handled by the existing admission path.
(assert-event
 (let ((name (coerce '(#\Page #\a #\Tab #\b #\Page) 'string)))
  (equal (fn2-startup-groups-from-text nil
          (concatenate 'string " " name " "))
         (list (list :groups (cons name 1))))))
