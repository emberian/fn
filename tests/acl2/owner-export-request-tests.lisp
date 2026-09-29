; tests/acl2/owner-export-request-tests.lisp -- teeth for
; books/owner-export-request.lisp (row S3, lane operability-4).

(in-package "ACL2")
(include-book "../../books/owner-export-request")

; The request's words, each observation pair.
(assert-event (equal (fn-oex-request-word nil nil) :requested))
(assert-event (equal (fn-oex-request-word t nil) :export-in-flight))
(assert-event (equal (fn-oex-request-word nil t) :archive-exists))
(assert-event (equal (fn-oex-request-word t t) :export-in-flight))

(assert-event (equal (fn-oex-request-status :requested) :accepted))
(assert-event (equal (fn-oex-request-status :export-in-flight) :refused))
(assert-event (equal (fn-oex-request-status :archive-exists) :refused))

; KEYSTONE fn-oex-one-export-in-flight, reachable positive witness: the
; complete antecedent (an export in flight, DIR absent) and the complete
; conclusion (the word is :export-in-flight, so not :requested).
(assert-event (and (equal (fn-oex-request-word t nil) :export-in-flight)
                   (not (equal (fn-oex-request-word t nil) :requested))))
; Hypothesis-removal witness: with no export in flight the same DIR
; observation is :requested (the omitted hypothesis fails, the conclusion
; fails).
(assert-event (and (not (equal (fn-oex-request-word nil nil) :export-in-flight))
                   (equal (fn-oex-request-word nil nil) :requested)))

; The status words.
(assert-event (equal (fn-oex-status-word t nil) :in-flight))
(assert-event (equal (fn-oex-status-word t '(:done . 7)) :in-flight))
(assert-event (equal (fn-oex-status-word nil '(:done . 7)) :done))
(assert-event (equal (fn-oex-status-word nil '(:failed . :archive-write)) :failed))
(assert-event (equal (fn-oex-status-word nil nil) :idle))
(assert-event (equal (fn-oex-status-status :failed) :refused))
(assert-event (equal (fn-oex-status-status :done) :accepted))
(assert-event (equal (fn-oex-status-status :in-flight) :accepted))

; The client reads every word back from its reply octets; other octets are
; no word.
(assert-event (equal (fn-oex-word-of-octets (fn-nctrl-reason-word :requested)) :requested))
(assert-event (equal (fn-oex-word-of-octets (fn-nctrl-reason-word :export-in-flight))
                     :export-in-flight))
(assert-event (equal (fn-oex-word-of-octets (fn-nctrl-reason-word :archive-exists))
                     :archive-exists))
(assert-event (equal (fn-oex-word-of-octets (fn-nctrl-reason-word :in-flight)) :in-flight))
(assert-event (equal (fn-oex-word-of-octets (fn-nctrl-reason-word :done)) :done))
(assert-event (equal (fn-oex-word-of-octets (fn-nctrl-reason-word :failed)) :failed))
(assert-event (equal (fn-oex-word-of-octets (fn-nctrl-reason-word :idle)) :idle))
(assert-event (null (fn-oex-word-of-octets (fn-nctrl-reason-word :found))))
(assert-event (null (fn-oex-word-of-octets nil)))
(assert-event (null (fn-oex-word-of-octets '(120 121))))

; The lines name the reason and what it would take.
(assert-event (equal (fn-oex-request-line :requested "/srv/a")
                     "export requested archive=/srv/a: the owner is writing it while serving; this verb waits for the outcome"))
(assert-event (search "reason=export-in-flight" (fn-oex-request-line :export-in-flight "/srv/a")))
(assert-event (search "what it would take" (fn-oex-request-line :export-in-flight "/srv/a")))
(assert-event (equal (fn-oex-request-line :archive-exists "/srv/a")
                     "export refused reason=archive-exists: /srv/a exists; what it would take: another DIR, or remove it"))
(assert-event (search "uncertain" (fn-oex-request-line nil "/srv/a")))
(assert-event (equal (fn-oex-outcome-line :done "/srv/a")
                     "exported archive=/srv/a: complete (its MANIFEST is written; `store import' reads it)"))
(assert-event (search "no MANIFEST was written" (fn-oex-outcome-line :failed "/srv/a")))
(assert-event (search "still writing" (fn-oex-outcome-line :in-flight "/srv/a")))
(assert-event (search "uncertain" (fn-oex-outcome-line :bogus "/srv/a")))

; `store export --status' with no owner: a sentence by name.
(assert-event (and (stringp (fn-oex-status-no-owner-line))
                   (equal (search "reason=no-owner" (fn-oex-status-no-owner-line)) 22)))
