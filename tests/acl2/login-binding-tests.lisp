; Witnesses and teeth for books/login-binding.lisp.
;
; The signed article is the fixture books/peer-authored-accept's tests use:
; *pat-relayed* carries an FN-Authorship carrier by *tha-principal* (32
; octets of 7), and under *pat-snapshots* fn-pa-current-plan accepts it
; (:ok ...).  *tha-root-source* is the same article with no carrier.
(in-package "ACL2")
(include-book "../../books/login-binding")
(include-book "peer-authored-accept-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *lbt-login* (fn-record-string-octets "ember"))
(defconst *lbt-other-login* (fn-record-string-octets "guest"))
(defconst *lbt-other-principal* (make-list 32 :initial-element 9))
(defconst *lbt-bindings*
  (list (cons *lbt-login* *tha-principal*)
        (cons *lbt-other-login* *lbt-other-principal*)))

; The policy as `fn policy set posting-policy bound-logins' records it.
(defconst *lbt-cfg-on*
  (fn-cfg-make 1 (fn-cfg-apply-delta
                  (fn-cfg-empty-value) 1 0
                  (fn-cfg-set-policy "posting-policy" "bound-logins"))))
(defconst *lbt-cfg-off* (fn-cfg-initial))
(assert-event (fn-lb-policy-onp *lbt-cfg-on*))
(assert-event (not (fn-lb-policy-onp *lbt-cfg-off*)))

; An owner whose submission in flight came from connection 5, authenticated
; as LOGIN (the AUTHINFO PASS branch leaves the USER name and the principal
; in the auth session).
(defun lbt-owner (login authenticatedp)
  (fn-own-make nil nil
               (list (fn-own-conn-make
                      5 0 0 nil
                      (fn-auth-make-session nil nil login
                                            (if authenticatedp
                                                (make-list 32 :initial-element 1)
                                              nil)
                                            nil nil)
                      nil nil nil))
               6 8 nil nil nil nil nil nil
               (fn-own-sub-make 5 0 0 nil) nil))
(defconst *lbt-o* (lbt-owner *lbt-login* t))
(defconst *lbt-o-guest* (lbt-owner *lbt-other-login* t))
(defconst *lbt-o-unauthenticated* (lbt-owner *lbt-login* nil))
(defconst *lbt-o-control*
  (fn-own-make nil nil nil 6 8 nil nil nil nil nil nil
               (fn-own-sub-make *fn-own-control-id* 0 0 nil) nil))
(assert-event (equal (fn-lb-inflight-login *lbt-o*) *lbt-login*))
(assert-event (null (fn-lb-inflight-login *lbt-o-unauthenticated*)))
(assert-event (null (fn-lb-inflight-login *lbt-o-control*)))

; A macro, not a constant: the plan decodes through attached codecs, which
; a defconst may not call.
(defmacro lbt-plan () '(fn-pa-current-plan *pat-relayed* *pat-snapshots* nil nil))
(assert-event (equal (car (lbt-plan)) :ok))

; --- fn-lb-bound-login-accepted-signed-article-carries-its-principal ------
; Witness: ember is bound to the fixture's principal, signs with it, passes
; and the plan accepts with that principal.
(assert-event
 (equal (fn-lb-owner-gate *lbt-o* *lbt-cfg-on* *lbt-bindings* *pat-relayed*)
        (list :pass *lbt-login* *tha-principal*)))
(assert-event (equal (nth 2 (lbt-plan)) *tha-principal*))
; Without the policy: guest (bound to another principal) passes and the
; accepted principal is not guest's binding.
(assert-event
 (equal (car (fn-lb-owner-gate *lbt-o-guest* *lbt-cfg-off* *lbt-bindings*
                               *pat-relayed*))
        :pass))
(must-fail
 (assert-event (equal (nth 2 (lbt-plan))
                      (fn-lb-binding (fn-lb-inflight-login *lbt-o-guest*)
                                     *lbt-bindings*))))
; Without the gate's pass: under the policy guest is refused, and the plan
; alone would still accept a principal that is not guest's.
(assert-event
 (equal (fn-lb-owner-gate *lbt-o-guest* *lbt-cfg-on* *lbt-bindings*
                          *pat-relayed*)
        (list :refused :login-not-bound *lbt-other-login*)))
(must-fail
 (assert-event
  (equal (car (fn-lb-owner-gate *lbt-o-guest* *lbt-cfg-on* *lbt-bindings*
                                *pat-relayed*))
         :pass)))
; Without a binding (principal nil): ember unbound passes, and the accepted
; principal is not nil.
(assert-event
 (equal (car (fn-lb-owner-gate *lbt-o* *lbt-cfg-on* nil *pat-relayed*)) :pass))
(must-fail (assert-event (equal (nth 2 (lbt-plan)) nil)))
; Without the plan's :ok: no enrollment, the plan refuses, and its third
; element is not the principal.
(assert-event
 (equal (fn-pa-current-plan *pat-relayed* nil nil nil)
        (list :refused :local-enrollment)))
(must-fail
 (assert-event (equal (nth 2 (fn-pa-current-plan *pat-relayed* nil nil nil))
                      *tha-principal*)))

; --- fn-lb-bound-login-unsigned-article-is-refused -------------------------
(assert-event (equal (fn-pa-carrier-form *tha-root-source*) :absent))
(assert-event
 (equal (fn-lb-owner-gate *lbt-o* *lbt-cfg-on* *lbt-bindings* *tha-root-source*)
        (list :refused :login-unsigned *lbt-login*)))
; Without the policy, without a binding, or with a carrier: not refused so.
(must-fail
 (assert-event
  (equal (car (fn-lb-owner-gate *lbt-o* *lbt-cfg-off* *lbt-bindings*
                                *tha-root-source*))
         :refused)))
(must-fail
 (assert-event
  (equal (car (fn-lb-owner-gate *lbt-o-unauthenticated* *lbt-cfg-on*
                                *lbt-bindings* *tha-root-source*))
         :refused)))
(must-fail
 (assert-event
  (equal (fn-lb-owner-gate *lbt-o* *lbt-cfg-on* *lbt-bindings* *pat-relayed*)
         (list :refused :login-unsigned *lbt-login*))))

; --- fn-lb-bound-login-other-principal-is-refused --------------------------
; Witness above (guest).  Without the policy, without a binding, or with the
; carrier naming the binding: not refused.
(must-fail
 (assert-event
  (equal (car (fn-lb-owner-gate *lbt-o-guest* *lbt-cfg-off* *lbt-bindings*
                                *pat-relayed*))
         :refused)))
(must-fail
 (assert-event
  (equal (car (fn-lb-owner-gate *lbt-o-guest* *lbt-cfg-on* nil *pat-relayed*))
         :refused)))
(must-fail
 (assert-event
  (equal (car (fn-lb-owner-gate *lbt-o* *lbt-cfg-on* *lbt-bindings*
                                *pat-relayed*))
         :refused)))

; --- fn-lb-policy-off-never-refuses / fn-lb-unbound-login-never-refuses ----
(assert-event
 (equal (car (fn-lb-owner-gate *lbt-o* *lbt-cfg-off* *lbt-bindings*
                               *tha-root-source*))
        :pass))
(assert-event
 (equal (car (fn-lb-owner-gate *lbt-o-control* *lbt-cfg-on* *lbt-bindings*
                               *tha-root-source*))
        :pass))
; With the policy and a binding, both refuse (the witnesses above): the
; hypothesis is what makes them pass.
(must-fail
 (assert-event
  (equal (car (fn-lb-owner-gate *lbt-o* *lbt-cfg-on* *lbt-bindings*
                                *tha-root-source*))
         :pass)))

; --- the verdict line names the login --------------------------------------
(assert-event
 (equal (fn-record-octets-string
         (fn-lb-verdict-line
          (fn-lb-owner-gate *lbt-o-guest* *lbt-cfg-on* *lbt-bindings*
                            *pat-relayed*)))
        "post login=guest refused login-not-bound"))
(assert-event
 (equal (fn-record-octets-string
         (fn-lb-verdict-line
          (fn-lb-owner-gate *lbt-o* *lbt-cfg-on* *lbt-bindings*
                            *tha-root-source*)))
        "post login=ember refused login-unsigned"))
(assert-event
 (equal (fn-record-octets-string
         (fn-lb-verdict-line
          (fn-lb-owner-gate *lbt-o* *lbt-cfg-on* *lbt-bindings* *pat-relayed*)))
        "post login=ember bound=0707070707070707070707070707070707070707070707070707070707070707"))
(assert-event
 (null (fn-lb-verdict-line
        (fn-lb-owner-gate *lbt-o-control* *lbt-cfg-on* *lbt-bindings*
                          *pat-relayed*))))

; The two refusal words reach their own 441 lines.
(assert-event (equal (fn-pa-served-word :refused :login-not-bound)
                     :login-not-bound))
(assert-event
 (equal (fn-post-store-refusal-line :login-not-bound)
        "441 posting failed; the login is not bound to this signing principal"))
(assert-event
 (equal (fn-post-store-refusal-line :login-unsigned)
        "441 posting failed; this login posts only articles signed by its bound principal"))
