(in-package "ACL2")
(include-book "../../books/consumer-remote-report-profile")

; Current-C first match, both dimensions from ONE captured key/generation.
(assert-event
 (let* ((start (fn-crcol-policy-begin '(source) 9
                '(("other" "" "" 1) ("max-remote-report-items" "" "" 3)
                  ("max-remote-report-octets" "" "" 4096))))
        (a (fn-crcol-policy-tick (cadr start) '(source) 9))
        (b (fn-crcol-policy-tick (cadr a) '(source) 9))
        (c (fn-crcol-policy-tick (cadr b) '(source) 9))
        (d (fn-crcol-policy-tick (cadr c) '(source) 9)))
  (and (equal (car a) :yield) (equal (car b) :yield) (equal (car c) :yield)
       (equal (car d) :ready)
       (equal (fn-crcol-policy-finish (cadr d) '(source) 9) '(:report-policy 3 4096))
       (equal (fn-crcol-policy-finish (cadr d) '(source) 10)
              '(:refused :remote-report-policy-source-changed))
       (equal (fn-crcol-policy-tick (cadr b) '(source) 10)
              '(:refused :remote-report-policy-source-changed)))))
(assert-event
 (and (equal (fn-crcol-policy-tick (fn-crcol-policy-state '(source) 9 nil 3 nil :lookup) '(source) 9)
             '(:refused :remote-report-limit-missing))
      (equal (fn-crcol-policy-verdict 0 4096) '(:refused :remote-report-policy-unsupported))
      (equal (fn-crcol-policy-verdict 3 4294967295) '(:refused :remote-report-policy-unsupported))
      (equal (fn-crcol-config-proposals 3 4096)
             (list :config-proposals (fn-cfg-set-limit "max-remote-report-items" 3)
                   (fn-cfg-set-limit "max-remote-report-octets" 4096)))
      (equal (fn-crcol-runtime-verdict '(:report-policy 3 4096))
             '(:unavailable :remote-report-runtime-representation))))
