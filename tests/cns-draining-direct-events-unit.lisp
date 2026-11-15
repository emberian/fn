; Metadata producer controls only, not a served CNS semantics witness.
(in-package "ACL2")
(include-book "../books/cns-draining-direct-events")

; Nested MV/LET bindings must make NS consume the actual WS result.
(defconst *fn2-cns-draining-sites-fixture*
 '((lambda (ws-output)
     ((lambda (next-core)
       (fn2-cns-release-ns '12 '1 '4 id '1 next-core))
      (mv-nth '1 ws-output)))
   (fn2-core-release '11 '1 '4 id '1 fn2-core)))
(defconst *fn2-cns-draining-sites-before*
 '(fn2-core-release '11 '1 '4 id '1 core))
(defconst *fn2-cns-draining-sites-after*
 `(fn2-cns-release-ns '12 '1 '4 id '1
    (mv-nth '1 ,*fn2-cns-draining-sites-before*)))
(assert-event
 (equal (fn2-cns-draining-call-sites *fn2-cns-draining-sites-fixture* '((fn2-core . core)))
        (list *fn2-cns-draining-sites-before* *fn2-cns-draining-sites-after*)))
(assert-event
 (and (fn2-cns-draining-sites-closedp
        (list *fn2-cns-draining-sites-before* *fn2-cns-draining-sites-after*))
      (fn2-cns-draining-second-statep
        *fn2-cns-draining-sites-before* *fn2-cns-draining-sites-after*)
      (not (fn2-cns-draining-second-statep
             *fn2-cns-draining-sites-before*
             '(fn2-cns-release-ns '12 '1 '4 id '1 core)))
      (not (fn2-cns-draining-sites-closedp
             '((fn2-cns-release-ns '12 '1 '4 id '1 dropped-core-binding))))))
; Literal data is not an executable effect call.
(assert-event
 (not (fn2-cns-draining-call-sites
        ''(fn2-core-release '11 '1 '4 id '1 fn2-core) '((fn2-core . core)))))
