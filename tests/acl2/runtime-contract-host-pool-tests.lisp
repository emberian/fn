; Closed witnesses for KL7 and the retained ARTICLE/pool keystones.
(in-package "ACL2")
(include-book "../../books/runtime-contract-host-pool")
(defconst *pb-p* (update-nth *fn-bs-pf-max-article-octets* 1 *fn-bs-profile-development*))
(defconst *pb-cfg* '(2 nil 0 0 nil 0 0 0 0 20 2 nil 0 1000))

; Witnesses: OVER dominates ARTICLE and h is the first pool buffer.
(defconst *pb-rtc* (fn-hl-rtc-config *pb-p* *pb-cfg* 4 1 1 16))
(assert-event (and (<= (fn-rtc-nhome *pb-rtc*) (nfix 3))
                   (<= (fn-ovr-over-capl-of *pb-p* *pb-cfg*) (fn-rtc-buf-cap 3 *pb-rtc*))))
(assert-event (and (posp (fn-hl-article-capl *pb-p* 4))
                   (<= (fn-hl-article-capl *pb-p* 4)
                       (+ (* 2 (nfix (fn-bs-profile-max-article-octets *pb-p*))) *fn-cbud-reply-status-octets*))))
(assert-event (<= (* (fn-rtc-npool *pb-rtc*) (fn-rtc-capl *pb-rtc*)) (fn-mm-large-pool *pb-p* *pb-cfg*)))

; KL7 hypothesis removal: a home buffer is below nhome and cannot hold this line.
(assert-event (and (not (<= (fn-rtc-nhome *pb-rtc*) (nfix 0)))
                   (not (<= (fn-ovr-over-capl-of *pb-p* *pb-cfg*)
                            (fn-rtc-buf-cap 0 *pb-rtc*)))))
