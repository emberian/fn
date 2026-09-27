(in-package "ACL2")
(include-book "../../books/native-hybrid-control")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "must-fail-checked")
(include-book "../../books/codec-attach")

(defconst *nhc-principal* (make-list 32 :initial-element 1))
(defconst *nhc-ed-key* (make-list 32 :initial-element 2))
(defconst *nhc-ml-key* (make-list 1952 :initial-element 3))
(defconst *nhc-ed-signature* (make-list 64 :initial-element 4))
(defconst *nhc-ml-signature* (make-list 3309 :initial-element 5))

(assert-equal
 (fn-native-hybrid-control-enroll-decode
  (fn-native-hybrid-control-enroll-encode
   7 *nhc-principal* *nhc-ed-key* *nhc-ml-key*))
 (list :hybrid-enroll 7 *nhc-principal* *nhc-ed-key* *nhc-ml-key*))

(assert-equal
 (fn-native-hybrid-control-author-decode
  (fn-native-hybrid-control-author-encode
   7 '(65 13 10) *nhc-ed-signature* *nhc-ml-signature*
   (fn-record-string-octets "/tmp/ml-public.pem")))
 (list :hybrid-author 7 '(65 13 10) *nhc-ed-signature* *nhc-ml-signature*
       (fn-record-string-octets "/tmp/ml-public.pem")))

(assert-equal
 (fn-native-hybrid-control-enroll-encode
  7 '(1) *nhc-ed-key* *nhc-ml-key*)
 :bad)

(assert-equal
 (fn-native-hybrid-control-revoke-decode
  (fn-native-hybrid-control-revoke-encode 8 *nhc-principal*))
 (list :hybrid-revoke 8 *nhc-principal*))

(assert-equal
 (fn-native-hybrid-control-revoke-encode 8 '(1)) :bad)

(assert-equal
 (fn-native-hybrid-control-enroll-decode
  (fn-native-hybrid-control-revoke-encode 8 *nhc-principal*))
 nil)

; D27 (PRF-091), then PKT-codex-003 (Mini/DREGG, 2026-09-27): the author
; request's source field is the frame's u32 payload less the other four
; fields, not the v1 carrier's 65 535.  A 65 536-octet source (the first v2
; length, refused before) round-trips, and the request covers every source a
; Store could hold.
(defconst *nhc-v1-source* (make-list 65535 :initial-element 65))
(defconst *nhc-ml-path* (fn-record-string-octets "/tmp/ml-public.pem"))
(assert-equal
 (fn-native-hybrid-control-author-decode
  (fn-native-hybrid-control-author-encode
   7 (cons 65 *nhc-v1-source*) *nhc-ed-signature* *nhc-ml-signature*
   *nhc-ml-path*))
 (list :hybrid-author 7 (cons 65 *nhc-v1-source*) *nhc-ed-signature*
       *nhc-ml-signature* *nhc-ml-path*))
(assert-event (equal *fn-nhctrl-max-source* 4294963388))
(assert-event (equal *fn-nhctrl-max-payload* *fn-frame-max-payload*))
(assert-event (< *fn-article-max-octets* *fn-nhctrl-max-source*))
(assert-event (< *fn-hsig-v1-max-source* *fn-nhctrl-max-source*))
; The hybrid read bound never falls below the ordinary one, and a key
; request is within the command-frame floor of the ordinary bound.
(assert-event (<= (fn-nctrl-read-bound-for 1048576 4)
                  (fn-nhctrl-read-bound-for 1048576 4)))
(assert-event (<= (+ *fn-frame-overhead-octets* *fn-nhctrl-key-payload*)
                  *fn-nctrl-max-command-frame*))

; KEYSTONE fn-native-hybrid-control-author-request-within-read-bound,
; positive witness at A = 300 000, G = 0: a 300 000-octet source is a v2
; source; the request is formed (not :bad), its source is at most A, and it
; is within the hybrid read bound.  It is PAST the ordinary FNCT bound at
; the same profile, so the author term of the hybrid bound is what admits it.
(defconst *nhc-v2-source* (make-list 300000 :initial-element 66))
(defun nhc-v2-request ()
  (fn-native-hybrid-control-author-encode
   7 *nhc-v2-source* *nhc-ed-signature* *nhc-ml-signature* *nhc-ml-path*))
; One evaluation (the request's digest runs through the SHA-256 attachment,
; which a defconst may not call), every literal checked on it.
(assert-event
 (let ((request (nhc-v2-request)))
   (and (natp 300000)
        (<= (len *nhc-v2-source*) 300000)
        (not (equal request :bad))
        (<= (len request) (fn-nhctrl-read-bound-for 300000 0))
        (< (fn-nctrl-read-bound-for 300000 0) (len request))
        (equal (fn-native-hybrid-control-author-decode request)
               (list :hybrid-author 7 *nhc-v2-source* *nhc-ed-signature*
                     *nhc-ml-signature* *nhc-ml-path*))
; Hypothesis-removal witness (omit (<= (len source) a)): at A = 1 000 the
; retained hypotheses hold (A natural, the request formed), the omitted one
; fails, and so does the conclusion: the request is past the read bound.
; The owner's read refuses it; a source past A is never read whole.
        (natp 1000)
        (not (<= (len *nhc-v2-source*) 1000))
        (not (<= (len request) (fn-nhctrl-read-bound-for 1000 0))))))

; PKT-147 (control-across-peers): every signed-author refusal is named.
; Witnesses for fn-nhc-author-refusal-is-a-named-refusal (no hypotheses)
; and fn-nhc-author-refusal-names-an-unserved-group.
(assert-event (equal (fn-nhc-author-refusal :carrier :unknown-group) :unknown-group))
(assert-event (equal (fn-nhc-author-refusal :carrier :path-present) :carrier-refused))
(assert-event (equal (fn-nhc-author-refusal :carrier :oversize)
                     :article-exceeds-profile-bound))
(assert-event (equal (fn-nhc-author-refusal :enrollment nil) :author-not-enrolled))
(assert-event (equal (fn-nhc-author-refusal :source nil) :source-malformed))
(assert-event (equal (fn-nhc-author-refusal :filing :control-not-filed)
                     :control-not-filed))
(assert-event (equal (fn-nhc-author-refusal :filing :control-malformed)
                     :control-malformed))
(assert-event (equal (fn-nhc-author-refusal :event nil) :signed-event-not-formed))
(assert-event (equal (fn-native-control-status-exit-code
                      (fn-nhc-author-refusal :carrier :unknown-group))
                     1))
(assert-event (equal (fn-native-control-reply-decode
                      (fn-native-control-reply-encode
                       (fn-nhc-author-refusal :carrier :unknown-group)))
                     :unknown-group))
; The named words are refusals, and the vocabulary's non-refusals are not.
(must-fail-checked (assert-event (equal (fn-native-control-status-class :uncertain) :refused)))
(must-fail-checked (assert-event (equal (fn-nhc-author-refusal :carrier :path-present)
                                :unknown-group)))
