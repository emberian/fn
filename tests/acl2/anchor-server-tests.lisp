(in-package "ACL2")
(include-book "../../books/anchor-servers")
(include-book "std/testing/assert-bang" :dir :system)

(assert! (fn-anchor-server-namep *fn-anchor-server-int08h-name*))
(assert! (fn-anchor-server-namep *fn-anchor-server-cloudflare-name*))
(assert! (not (fn-anchor-server-namep '(117 110 107 110 111 119 110))))
(assert! (equal (fn-anchor-server-find '(117 110 107 110 111 119 110))
                '(:refused :unknown-anchor-server)))

(assert! (equal (nth 1 (fn-anchor-server-find *fn-anchor-server-int08h-name*))
                *fn-anchor-server-int08h-host*))
(assert! (equal (nth 2 (fn-anchor-server-find *fn-anchor-server-int08h-name*))
                2002))
(assert! (equal (nth 3 (fn-anchor-server-find *fn-anchor-server-int08h-name*))
                *fn-anchor-server-int08h-key*))
(assert! (member-equal
          (nth 3 (fn-anchor-server-find *fn-anchor-server-int08h-name*))
          (nth 4 (fn-anchor-server-find *fn-anchor-server-int08h-name*))))

; A one-octet change cannot silently select the int08h trust root.
(assert! (not (fn-anchor-server-namep '(105 110 116 48 56 105))))

(assert! (equal (len (fn-anchor-server-select
                      *fn-anchor-server-int08h-name* 5))
                9))
(assert! (equal (nth 5 (fn-anchor-server-select
                        *fn-anchor-server-int08h-name* 5))
                *fn-anchor-nonce-octets*))
(assert! (equal (nth 6 (fn-anchor-server-select
                        *fn-anchor-server-int08h-name* 5))
                *fn-anchor-wire-request-octets*))
(assert! (equal (nth 7 (fn-anchor-server-select
                        *fn-anchor-server-int08h-name* 5))
                *fn-anchor-wire-max-response*))
(assert! (equal (fn-anchor-server-select
                 *fn-anchor-server-int08h-name* 0)
                '(:refused :anchor-timeout)))
(assert! (equal (fn-anchor-server-select
                 *fn-anchor-server-int08h-name* 61)
                '(:refused :anchor-timeout)))
