; Witnesses and teeth for O2, read-only groups (PRF-196): books/config.lisp
; (:set-group-status, code 21), books/config-invariants.lisp
; `fn-cfg-set-group-status-sets-the-status', books/owner-agent.lisp (the
; closed list in the posting configuration), books/group-status.lisp (the
; gate) and books/nntp-post.lisp `fn-nntp-post-step' (the host-called step:
; POST's 441 and LIST ACTIVE's status field from one list).
(in-package "ACL2")
(include-book "../../books/nntp-post")
(include-book "../../books/config-invariants")
(include-book "../../books/owner-agent")
(include-book "../../books/native-admin")
(include-book "std/testing/must-fail" :dir :system)

(defun gst-o (s) (declare (xargs :guard (stringp s))) (fn-nntp-string-octets s))

; ---------------------------------------------------------------------------
; 1. The configuration: the delta, its code, its fold and its admission.

(defconst *gst-stamp* (fn-clock-observation 0 0 0 nil))
(defconst *gst-v1*
  (fn-cfg-apply (fn-cfg-empty-value) 1 *gst-stamp*
                (list (fn-cfg-create-group "fn.test" *fn-cfg-default-policy-id*)
                      (fn-cfg-create-group "fn.announce" *fn-cfg-default-policy-id*))))
(defconst *gst-v2*
  (fn-cfg-apply-delta *gst-v1* 2 *gst-stamp*
                      (fn-cfg-set-group-status "fn.announce" "n")))
(assert-event (fn-cfg-valuep *gst-v1*))
(assert-event (fn-cfg-valuep *gst-v2*))
(assert-event (equal (fn-cfg-kind-code :set-group-status) 21))
(assert-event (equal (fn-cfg-code-kind 21) :set-group-status))
(assert-event (fn-cfg-deltap (fn-cfg-set-group-status "fn.announce" "n")))
; Admitted for a live group and "y" or "n"; refused by name otherwise.
(assert-event (null (fn-cfg-delta-reason *gst-v1* 2 *gst-stamp* 0 512
                                         (fn-cfg-set-group-status "fn.announce" "n"))))
(assert-event (equal (fn-cfg-delta-reason *gst-v1* 2 *gst-stamp* 0 512
                                          (fn-cfg-set-group-status "fn.absent" "n"))
                     :no-such-group))
(assert-event (equal (fn-cfg-delta-reason *gst-v1* 2 *gst-stamp* 0 512
                                          (fn-cfg-set-group-status "fn.announce" "m"))
                     :group-status))
; The fold: fn.announce is "n", fn.test stays "y", the closed list is the one.
(assert-event (equal (fn-cfg-group-status *gst-v1* 2 "fn.announce") "y"))
(assert-event (equal (fn-cfg-group-status *gst-v2* 2 "fn.announce") "n"))
(assert-event (equal (fn-cfg-group-status *gst-v2* 2 "fn.test") "y"))
(assert-event (equal (fn-cfg-closed-names *gst-v2* 2) '("fn.announce")))
(assert-event (equal (fn-cfg-group-names *gst-v2* 2) (fn-cfg-group-names *gst-v1* 2)))
; "y" opens it again.
(assert-event (equal (fn-cfg-group-status
                      (fn-cfg-apply-delta *gst-v2* 3 *gst-stamp*
                                          (fn-cfg-set-group-status "fn.announce" "y"))
                      3 "fn.announce")
                     "y"))
; The record round trip: the delta survives the codec (replay reads it).
(defconst *gst-record*
  (fn-cfg-record-make 1 5 2 (list (fn-cfg-set-group-status "fn.announce" "n"))
                      *gst-stamp*))
(assert-event (equal (fn-cfg-decode-exact (fn-cfg-encode *gst-record*))
                     (fn-record-parse-ok *gst-record* nil)))

; KEYSTONE fn-cfg-set-group-status-sets-the-status: reachable witness, every
; hypothesis and both conclusions asserted.
(assert-event
 (let ((v *gst-v1*) (gen 2) (name "fn.announce") (status "n") (other "fn.test"))
   (and (fn-cfg-valuep v)
        (fn-cfg-group-livep v gen name)
        (member-equal status '("y" "n"))
        (equal (fn-cfg-group-status
                (fn-cfg-apply-delta v gen *gst-stamp*
                                    (fn-cfg-set-group-status name status))
                gen name)
               status)
        (not (equal other name))
        (equal (fn-cfg-group-status
                (fn-cfg-apply-delta v gen *gst-stamp*
                                    (fn-cfg-set-group-status name status))
                gen other)
               (fn-cfg-group-status v gen other)))))
; Without the liveness hypothesis: an absent group is not set (the other
; hypotheses hold, the conclusion fails).
(assert-event (not (fn-cfg-group-livep *gst-v1* 2 "fn.absent")))
(must-fail
 (assert-event (equal (fn-cfg-group-status
                       (fn-cfg-apply-delta *gst-v1* 2 *gst-stamp*
                                           (fn-cfg-set-group-status "fn.absent" "n"))
                       2 "fn.absent")
                      "n")))
; Without the status hypothesis: "m" is not a status fn serves; the fold
; reads it as "y", so the conclusion (status = "m") fails.
(assert-event (fn-cfg-group-livep *gst-v1* 2 "fn.announce"))
(must-fail
 (assert-event (equal (fn-cfg-group-status
                       (fn-cfg-apply-delta *gst-v1* 2 *gst-stamp*
                                           (fn-cfg-set-group-status "fn.announce" "m"))
                       2 "fn.announce")
                      "m")))
; Without the value hypothesis (CORRUPTED STATE, labelled): a group table
; holding a non-entry atom before the entry.  Not reachable by replay.
(defconst *gst-corrupt*
  (fn-cfg-value-make (cons nil (fn-cfg-groups *gst-v1*)) 0 nil nil nil nil nil nil nil nil))
(assert-event (not (fn-cfg-valuep *gst-corrupt*)))

; ---------------------------------------------------------------------------
; 2. The operator verb: `group policy NAME n|y' stages exactly the delta.

(defun gst-argv (words)
  (if (consp words) (cons (gst-o (car words)) (gst-argv (cdr words))) nil))
(defconst *gst-plan* (fn-native-admin-plan (gst-argv '("group" "policy" "fn.announce" "n"))))
(assert-event (equal (fn-native-admin-result-status *gst-plan*) :accepted))
(assert-event (equal (fn-native-admin-plan-deltas *gst-plan*)
                     (list (fn-cfg-set-group-status "fn.announce" "n"))))
(assert-event (fn-cfg-delta-listp (fn-native-admin-plan-deltas *gst-plan*)))
(assert-event (not (equal (fn-native-admin-result-status
                           (fn-native-admin-plan (gst-argv '("group" "policy" "fn.announce" "m"))))
                          :accepted)))

; ---------------------------------------------------------------------------
; 3. The posting configuration the owner installs carries the closed list.

(defconst *gst-cfg-record* (fn-cfg-make 2 *gst-v2*))
(defconst *gst-post-config* (fn-oag-post-config *gst-cfg-record* 32768))
(assert-event (equal (fn-inj-config-closed *gst-post-config*)
                     (list (gst-o "fn.announce"))))
(assert-event (fn-inj-configp *gst-post-config*))

; ---------------------------------------------------------------------------
; 4. The served POST step and LIST ACTIVE, one list.

(defconst *gst-agent* (gst-o "fn.example.invalid"))
(defconst *gst-closed* (list (gst-o "fn.announce")))
(defconst *gst-cfg*
  (fn-inj-make-config-closed t *gst-agent*
                             (list (gst-o "fn.test") (gst-o "fn.announce"))
                             32768 *gst-closed*))
(defconst *gst-open-cfg*
  (fn-inj-make-config t *gst-agent*
                      (list (gst-o "fn.test") (gst-o "fn.announce")) 32768))
(defconst *gst-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defun gst-article (newsgroups extra)
  (declare (xargs :guard (and (stringp newsgroups) (stringp extra))))
  (gst-o (concatenate 'string
                      "From: poster@example.invalid" (coerce '(#\Return #\Newline) 'string)
                      "Subject: hello" (coerce '(#\Return #\Newline) 'string)
                      "Newsgroups: " newsgroups (coerce '(#\Return #\Newline) 'string)
                      extra
                      (coerce '(#\Return #\Newline) 'string)
                      "Hello." (coerce '(#\Return #\Newline) 'string))))
(defconst *gst-crlf* (coerce '(#\Return #\Newline) 'string))
(defconst *gst-to-announce* (gst-article "fn.announce" ""))
(defconst *gst-to-test* (gst-article "fn.test" ""))
(defconst *gst-cross* (gst-article "fn.test,fn.announce" ""))
(defconst *gst-cancel*
  (gst-article "fn.announce"
               (concatenate 'string "Control: cancel <x@example.invalid>" *gst-crlf*)))
(defconst *gst-supersede*
  (gst-article "fn.announce"
               (concatenate 'string "Supersedes: <x@example.invalid>" *gst-crlf*)))

; The gate: an ordinary article naming a closed group (alone or cross-posted)
; is refused; one naming only open groups passes; a cancel is not a posting;
; a Supersedes article is.
(assert-event (equal (fn-gst-post-gate *gst-to-announce* *gst-cfg*) (list (gst-o "fn.announce"))))
(assert-event (equal (fn-gst-post-gate *gst-cross* *gst-cfg*) (list (gst-o "fn.announce"))))
(assert-event (null (fn-gst-post-gate *gst-to-test* *gst-cfg*)))
(assert-event (null (fn-gst-post-gate *gst-cancel* *gst-cfg*)))
(assert-event (equal (fn-gst-post-gate *gst-supersede* *gst-cfg*) (list (gst-o "fn.announce"))))
; With no closed group nothing is gated.
(assert-event (null (fn-gst-post-gate *gst-to-announce* *gst-open-cfg*)))

; KEYSTONE fn-gst-post-gate-refuses-exactly-a-listed-n-group: both
; directions, reachable (no hypotheses).
(assert-event (and (fn-gst-post-gate *gst-to-announce* *gst-cfg*)
                   (fn-gst-some-closedp (fn-gst-named-groups *gst-to-announce* *gst-cfg*)
                                        (fn-inj-config-closed *gst-cfg*))))
(assert-event (and (not (fn-gst-post-gate *gst-to-test* *gst-cfg*))
                   (not (fn-gst-some-closedp (fn-gst-named-groups *gst-to-test* *gst-cfg*)
                                             (fn-inj-config-closed *gst-cfg*)))))

; The host-called step: an archive serving both groups.
(defconst *gst-archive* (fn-initial-state '("fn.announce" "fn.test")))
(defconst *gst-s0* (fn-post-open-session *gst-archive*))
(defconst *gst-awaiting*
  (fn-post-result-session
   (fn-nntp-post-step *gst-s0* *gst-archive* *gst-cfg* *gst-obs* *gst-obs*
                      (list :command (gst-o "POST")))))
(assert-event (fn-post-session-awaiting *gst-awaiting*))
(defun gst-post (source cfg)
  (fn-nntp-post-step *gst-awaiting* *gst-archive* cfg *gst-obs* *gst-obs*
                     (list :article (list source))))
(defconst *gst-read-only-line*
  "441 posting failed; a group this article names is read-only here (LIST ACTIVE status n)")
(defun gst-reply (text)
  (list (fn-nntp-reply-effect (fn-nntp-crlf (fn-nntp-string-octets text)))))
; POST to the closed group: 441 by name, no submission.
(assert-event (equal (fn-post-result-effects (gst-post *gst-to-announce* *gst-cfg*))
                     (gst-reply *gst-read-only-line*)))
(assert-event (null (fn-post-result-submission (gst-post *gst-to-announce* *gst-cfg*))))
; POST to the open group: a submission (the host owes the durable attempt).
(assert-event (fn-post-result-submission (gst-post *gst-to-test* *gst-cfg*)))
; The same article with no closed group: a submission.
(assert-event (fn-post-result-submission (gst-post *gst-to-announce* *gst-open-cfg*)))

; LIST ACTIVE on the same connection configuration: fn.announce is "n",
; fn.test is "y"; with none closed, both "y" (the earlier answer).
(defun gst-list (cfg words)
  (fn-post-result-effects
   (fn-nntp-post-step *gst-s0* *gst-archive* cfg *gst-obs* *gst-obs*
                      (list :command (gst-o words)))))
(defun gst-listing (lines)
  (fn-nntp-result-effects
   (fn-nntp-multi nil "215 list of active newsgroups follows" lines)))
(assert-event (equal (gst-list *gst-cfg* "LIST")
                     (gst-listing (list (gst-o "fn.announce 0 1 n")
                                        (gst-o "fn.test 0 1 y")))))
(assert-event (equal (gst-list *gst-cfg* "LIST") (gst-list *gst-cfg* "LIST ACTIVE")))
(assert-event (equal (gst-list *gst-cfg* "LIST ACTIVE fn.a*")
                     (gst-listing (list (gst-o "fn.announce 0 1 n")))))
(assert-event (equal (gst-list *gst-open-cfg* "LIST ACTIVE")
                     (gst-listing (list (gst-o "fn.announce 0 1 y")
                                        (gst-o "fn.test 0 1 y")))))
