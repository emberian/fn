; Teeth for books/owner-maintenance-request.lisp (row S3, lane operability-2).
(in-package "ACL2")
(include-book "../../books/owner-maintenance-request")

; The route: a live owner answers, a held lock refuses by name, and only a
; free lock (no owner, or a crashed owner's stale socket) starts the offline
; executor.
(assert-event (equal (fn-omr-route :live) :owner))
(assert-event (equal (fn-omr-route :held) :held))
(assert-event (equal (fn-omr-route :stale) :offline))
(assert-event (equal (fn-omr-route :offline) :offline))

; `recover': accepted on a live owner (a status read follows), refused by
; name with what it would take on a held lock, no line offline.
(assert-event (equal (fn-omr-recover-status :owner) :accepted))
(assert-event (equal (fn-omr-recover-status :held) :refused))
(assert-event (equal (fn-omr-recover-status :offline) :offline))
(assert-event (equal (fn-omr-recover-line :owner)
                     "recover accepted owner=serving: the owner's open recovered the store and it is serving; nothing to recover; its status follows"))
(assert-event (equal (fn-omr-recover-line :held)
                     "recover refused reason=owner-holds-the-store: an owner holds the writer lock and answers nothing on its control socket; what it would take: wait for its start or its stop to finish, or stop it"))
(assert-event (null (fn-omr-recover-line :offline)))

; KEYSTONE fn-omr-inspect-live-is-the-offline-report, positive witnesses:
; the owner's lookup found (and not found), sent as the reasoned reply's
; word, renders the offline report entire: exit, verdict and line.
(defconst *omr-msgid* (fn-record-string-octets "<a@b.example>"))
(assert-event
 (equal (fn-omr-inspect-live-report *omr-msgid*
                                    (fn-nctrl-reason-word (fn-omr-inspect-word t)))
        (fn-native-operator-inspect-report *omr-msgid* t)))
(assert-event
 (equal (fn-omr-inspect-live-report *omr-msgid*
                                    (fn-nctrl-reason-word (fn-omr-inspect-word nil)))
        (fn-native-operator-inspect-report *omr-msgid* nil)))
(assert-event (equal (car (fn-omr-inspect-live-report
                           *omr-msgid* (fn-nctrl-reason-word :found)))
                     0))
(assert-event (equal (car (fn-omr-inspect-live-report
                           *omr-msgid* (fn-nctrl-reason-word :absent)))
                     1))
; A word that is neither (a malformed owner) reads as absent: exit 1, never
; a claimed article.
(assert-event (equal (car (fn-omr-inspect-live-report
                           *omr-msgid* (fn-nctrl-reason-word :bogus)))
                     1))
; The wire status accepts exactly when the offline exit is 0.
(assert-event (equal (fn-omr-inspect-status (fn-omr-inspect-word t)) :accepted))
(assert-event (equal (fn-omr-inspect-status (fn-omr-inspect-word nil)) :refused))

; The stopped report: the covered sequence from a real header, the bound.
(defconst *omr-header* (fn-scc-header 0 1 100 12))
(assert-event (equal (len *omr-header*) *fn-scc-segment-header-octets*))
(assert-event (equal (fn-omr-covered-sequence *omr-header*) 12))
(assert-event (null (fn-omr-covered-sequence nil)))
(assert-event (null (fn-omr-covered-sequence '(1 2 3))))
(assert-event (equal *fn-omr-min-frame-octets* 42))
(assert-event (equal (fn-omr-transactions-at-most 12 420) 22))
(assert-event (equal (fn-omr-transactions-at-most nil 41) 0))
; KEYSTONE fn-omr-transactions-at-most-bounds-the-count, positive witness:
; 12 covered, 5 records of 42 octets each in a journal of 300 octets.
(assert-event (and (natp 12) (natp 5) (natp 300) (<= (* 5 42) 300)
                   (<= (+ 12 5) (fn-omr-transactions-at-most 12 300))))
; Hypothesis removal, the octet premise: 8 records cannot fit in 300 octets
; (8 * 42 = 336 > 300) and the bound does not cover them.
(assert-event (and (natp 12) (natp 8) (natp 300)
                   (not (<= (* 8 42) 300))
                   (not (<= (+ 12 8) (fn-omr-transactions-at-most 12 300)))))

; The stopped line is rendered from the header's sequence and the octets.
(assert-event
 (equal (fn-omr-stopped-line 12 420)
        (fn-record-string-octets
         "stopped checkpoint=12 journal-octets=420 transactions-at-most=22
")))
(assert-event
 (equal (fn-omr-stopped-line nil 41)
        (fn-record-string-octets
         "stopped checkpoint=none journal-octets=41 transactions-at-most=0
")))
; A foreign config.json is the open's own refusal, exit 1.
(assert-event (equal (car (fn-omr-stopped-report
                           (fn-record-string-octets "not a store") *omr-header* 0 nil))
                     1))
