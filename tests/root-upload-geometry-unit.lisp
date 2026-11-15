; ROOT's actual shared sizing decisions, not the donor cold payload policy.
; Source-prepared only; these do not admit or reserve foreground work.
(in-package "ACL2")
(include-book "../books/upload-page-geometry")
(assert-event (= *fn2-commit-extent-bytes* 65536))
(assert-event (and (not (fn2-am-manifestp 12289))
                   (not (fn2-am-manifestp 33032))
                   (not (fn2-am-manifestp 65536))
                   (fn2-am-manifestp 65537)))
; Distinguishes ROOT from the cold donor's three-unit raw/manifest boundary,
; including the full existing default article+generated Message-ID footprint.
(assert-event (= (fn2-upload-page-bytes 33032) *fn2-upload-page-manifest*))
(assert-event (= (fn2-upload-page-bytes 65536) *fn2-upload-page-manifest*))
(assert-event (= (fn2-upload-page-bytes 65537)
                 (+ *fn2-upload-page-manifest* *fn2-commit-unit-bytes*)))
(assert-event (= (fn2-upload-profile-article-max nil) *fn2-upload-article-max*))
(assert-event (= (fn2-upload-profile-article-max '((:article-max . 40000))) 40000))
(assert-event (= (fn2-upload-input-bound 40000 8192 8192) 16351))
(assert-event (and (fn2-upload-article-profilep nil)
                   (not (fn2-upload-article-profilep '((:article-max . -1))))))
