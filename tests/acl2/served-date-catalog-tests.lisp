; The two native post routes, on a reachable empty catalog/view.
(in-package "ACL2")
(include-book "../../books/served-catalog-chain")

; Full empty antecedent of the catalog noninterference theorem, and the
; carried restricted implementation's existing exact correspondence.
(assert-event
 (let* ((archive (fn-initial-state nil))
        (ps (fn-post-open-session archive))
        (config (fn-inj-make-config t '(102 110) nil 32768))
        (old (fn-clock-observation 1000000 843004800000 500 t))
        (now (fn-clock-observation 1061000 843004861000 500 t))
        (event '(:command (68 65 84 69)))
        (expected (fn-nntp-result-effects
                   (fn-nntp-date-response nil (fn-nntp-env now nil t)))))
   (and (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
        (equal (fn-scr-post-step ps archive nil nil config old now event 0 fn-arena fn-cat)
               (fn-scr-post-step ps archive nil nil config nil now event 0 fn-arena fn-cat))
        (equal (fn-post-result-effects
                (fn-scr-post-step ps archive nil nil config old now event 0 fn-arena fn-cat))
               expected)
        (equal (fn-post-result-effects
                (fn-pix-post-step-pinned ps archive nil nil config old now event fn-arena))
               expected)
        ; MUTATION: the old pinned-reading response differs on both routes.
        (not (equal (fn-nntp-result-effects
                     (fn-nntp-date-response nil (fn-nntp-env old nil t)))
                    expected)))))
