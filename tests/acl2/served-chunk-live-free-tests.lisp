; served-chunk-live-free-tests.lisp -- teeth for books/served-chunk-live-free
; (lane join-f2-3, 2026-09-29; PKT-731).  Owners from tests/acl2/owner-tests:
; *own-taken* (reader 3 pinned at version 2, the committed view at 2, the
; post of <three@example> taken) and *own-after-post* (the post's 240
; installed; the committed view at 3, reader 3's record untouched).

(in-package "ACL2")

(include-book "owner-tests")
(include-book "../../books/served-chunk-live-free")

(bpr-lift fn-own-read-tls-prefix 3)
(bpr-lift fn-scl-counted-selects-nothing-p 2)

(defconst *sclt-stat* (append (fn-nntp-string-octets "STAT <three@example>") '(13 10)))

(defun sclt-conn (o) (fn-own-find-conn 3 (fn-own-conns o)))

; The antecedent of fn-scl-own-read-tls-prefix-selecting-nothing-ignores-the-view
; with o = *own-taken*, o2 = *own-after-post*: every literal but the chunk's.
(defun sclt-retained (o o2)
  (and (sclt-conn o)
       (equal (sclt-conn o2) (sclt-conn o))
       (equal (fn-own-clock o2) (fn-own-clock o))
       (equal (fn-own-config o2) (fn-own-config o))
       (equal (fn-own-conn-live-session o2 (sclt-conn o))
              (fn-own-conn-live-session o (sclt-conn o)))))

(defun sclt-answer (octets o)
  (let ((r (in-arena-fn-own-read-tls-prefix *sr-arena* o 3 octets)))
    (list (fn-own-tls-result-consumed r) (fn-own-tls-result-effects r))))

; The two owners' committed views differ (so the witness is not vacuous).
(assert-event (not (equal (fn-own-view-live (fn-own-view *own-after-post*))
                          (fn-own-view-live (fn-own-view *own-taken*)))))

; Positive witness: STAT selects nothing; the complete antecedent holds and
; both owners answer 430 with the same consumed count.
(assert-event (sclt-retained *own-taken* *own-after-post*))
(assert-event (in-arena-fn-scl-counted-selects-nothing-p
               *sr-arena* (fn-own-tls-served-conn *own-taken* (sclt-conn *own-taken*)) *sclt-stat*))
(assert-event (equal (sclt-answer *sclt-stat* *own-after-post*)
                     (sclt-answer *sclt-stat* *own-taken*)))
(assert-event (equal (fn-own-take 3 (fn-served-reply-octets
                                     (cadr (sclt-answer *sclt-stat* *own-taken*))))
                     (fn-nntp-string-octets "430")))

; Hypothesis-removal witness (the chunk selects nothing): every retained
; literal holds, GROUP fails the chunk's, and the conclusion fails -- the
; reader at version 2 answers 211 2 1 2 over the old view and 211 3 1 3
; over the new.
(assert-event (sclt-retained *own-taken* *own-after-post*))
(assert-event (not (in-arena-fn-scl-counted-selects-nothing-p
                    *sr-arena* (fn-own-tls-served-conn *own-taken* (sclt-conn *own-taken*))
                    *own-group-octets*)))
(assert-event (not (equal (sclt-answer *own-group-octets* *own-after-post*)
                          (sclt-answer *own-group-octets* *own-taken*))))

; A2: the owner-configuration premise has teeth (ACCESS-REVOKE-PINNED).  Reader
; 2 of *own-c* is pinned where <one@example> is in its view.  *scla-o2* is
; *own-c* with a live configuration whose anonymous read rule names another
; group.  Every retained literal but the configuration holds and the chunk
; selects nothing, yet the answer changes: STAT 223 under the owner's own
; configuration, 430 under the revoking one (as served-access-revoke-tests).
(defconst *scla-live-b*
  (fn-inj-make-config-full t *own-agent*
                           (list (fn-nntp-string-octets "fn.letters")
                                 (fn-nntp-string-octets "fn.test"))
                           32768
                           (list nil nil *own-agent*
                                 (fn-cfg-access-table
                                  (list (fn-cfg-row-make "" "fn.nothing" "*" 3))))
                           nil))
(defconst *scla-o2* (fn-own-configure *own-c* *scla-live-b*))
(defconst *scla-stat* (append (fn-nntp-string-octets "STAT <one@example>") '(13 10)))
(defun scla-conn (o) (fn-own-find-conn 2 (fn-own-conns o)))
(assert-event (scla-conn *own-c*))
(assert-event (equal (scla-conn *scla-o2*) (scla-conn *own-c*)))
(assert-event (equal (fn-own-clock *scla-o2*) (fn-own-clock *own-c*)))
(assert-event (equal (fn-own-conn-live-session *scla-o2* (scla-conn *own-c*))
                     (fn-own-conn-live-session *own-c* (scla-conn *own-c*))))
(assert-event (not (equal (fn-own-config *scla-o2*) (fn-own-config *own-c*))))
(assert-event (in-arena-fn-scl-counted-selects-nothing-p
               *sr-arena* (fn-own-tls-served-conn *own-c* (scla-conn *own-c*)) *scla-stat*))
(defun scla-code (o)
  (let ((r (in-arena-fn-own-read-tls-prefix *sr-arena* o 2 *scla-stat*)))
    (fn-own-take 3 (fn-served-reply-octets (fn-own-tls-result-effects r)))))
(assert-event (equal (scla-code *own-c*) (fn-nntp-string-octets "223")))
(assert-event (equal (scla-code *scla-o2*) (fn-nntp-string-octets "430")))
