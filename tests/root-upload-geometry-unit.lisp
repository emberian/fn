; Paired rolling producer's SAME lower sizing decisions. Source-only controls.
; The physical extent is unchanged; raw commitment capacity is derived from
; actual trusted write resources, independently of the physical extent size.
(in-package "ACL2")
(include-book "../books/upload-page-geometry")
(assert-event (= *fn2-commit-extent-bytes* 65536))
(assert-event (= *fn2-upload-raw-bytes* (* *fn2-commit-write-resources* *fn2-commit-unit-bytes*)))
(assert-event (and (not (fn2-am-manifestp 12288))
                   (fn2-am-manifestp 12289)
                   (fn2-am-manifestp 33032)
                   (fn2-am-manifestp 65537)))
(assert-event (= (fn2-upload-page-bytes 33032)
                 (+ *fn2-upload-page-manifest* *fn2-commit-unit-bytes*)))
(assert-event (= *fn2-upload-page-source*
                 (+ *fn2-upload-page-stored-source* *fn2-upload-digest-octets*)))
(assert-event (= (fn2-upload-stream-page-bytes 33032)
                 (+ *fn2-upload-page-manifest* *fn2-upload-raw-bytes*
                    (* *fn2-commit-unit-bytes* (fn2-am-units 33032)))))
(assert-event (< (fn2-upload-page-bytes 33032) (fn2-upload-stream-page-bytes 33032)))
(assert-event (= (fn2-upload-profile-article-max nil) *fn2-upload-article-max*))
(assert-event (= (fn2-upload-profile-article-max '((:article-max . 40000))) 40000))
; Physical rolling windows do not impose a stored-data ceiling on the profile.
(assert-event (= (fn2-upload-input-bound 40000 8192 8192) 40000))
(assert-event (and (fn2-upload-article-profilep nil)
                   (not (fn2-upload-article-profilep '((:article-max . -1))))))
