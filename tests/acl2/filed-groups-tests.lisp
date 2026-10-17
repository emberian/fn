; Witnesses and teeth for books/filed-groups (O1 packets 1 and 2): each keystone's
; antecedent satisfied on a concrete article, the invariant refusing groups
; its header does not name, and the signed constructor's fixture
; (tests/acl2/hybrid-store-tests.lisp) satisfying SIGNED with the invariant.
(in-package "ACL2")
(include-book "hybrid-store-tests")
(include-book "peer-authored-accept-tests")

(defconst *o1-src*
  (fn-record-string-octets
   (concatenate 'string "From: a@b.example" (coerce '(#\Return #\Newline) 'string)
                "Newsgroups: fn.test,fn.letters" (coerce '(#\Return #\Newline) 'string)
                "Subject: s" (coerce '(#\Return #\Newline) 'string)
                "Message-ID: <w1@b.example>" (coerce '(#\Return #\Newline) 'string)
                (coerce '(#\Return #\Newline) 'string) "body" (coerce '(#\Return #\Newline) 'string))))
(defconst *o1-ctl*
  (fn-record-string-octets
   (concatenate 'string "From: a@b.example" (coerce '(#\Return #\Newline) 'string)
                "Newsgroups: fn.test" (coerce '(#\Return #\Newline) 'string)
                "Subject: cmsg cancel <w1@b.example>" (coerce '(#\Return #\Newline) 'string)
                "Control: cancel <w1@b.example>" (coerce '(#\Return #\Newline) 'string)
                "Message-ID: <c1@b.example>" (coerce '(#\Return #\Newline) 'string)
                (coerce '(#\Return #\Newline) 'string) "body" (coerce '(#\Return #\Newline) 'string))))

; the signed binding the keystone reads: groups as hybrid-store computes them
(assert-event (equal (fn-hsig-source-filed-groups *o1-src* (fn-hsig-authored-source-fields *o1-src*))
                     '("fn.test" "fn.letters")))
(assert-event (equal (fn-hsig-source-filed-groups *o1-ctl* (fn-hsig-authored-source-fields *o1-ctl*))
                     '("control.cancel")))

(assert-event (equal (len (fn-record-string-octets (fn-ctl-filing-group (fn-record-string-octets "checkgroups")))) 19))

; ---------------------------------------------------------------------------
; Packet 2.  Each keystone's whole implication on a concrete instance (its
; antecedent and its conclusion), and for the bounds a hypothesis-removal
; tooth: the hypothesis dropped, the other one kept, the conclusion false.
(defconst *o1p2-lim* (fn-article-limits 100 200 16384))
(defconst *o1p2-zero* (fn-article-limits 100 200 0))

(assert-event (null (fn-hsig-authorized-injected-carried-submission-event
                     2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
                     *hst-authored-source* *hst-injected-received* '("other")
                     *hst-injected-obligation* *hst-injected-subject* "release"
                     (fn-charge-for-payload (len *hst-injected-received*))
                     *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
                     :verified :verified *hst-injection-config*
                     *hst-injection-observation*)))

; P2-4 with a singleton longer than 19 octets at its own tightest limits:
; the bound comes from the header-charge disjunct, not the shortcut.
(defconst *o1p2-long*
  (fn-record-string-octets
   (concatenate 'string "From: a@b.example" (coerce '(#\Return #\Newline) 'string)
                "Newsgroups: comp.lang.lisp.franz.extra" (coerce '(#\Return #\Newline) 'string)
                "Subject: s" (coerce '(#\Return #\Newline) 'string)
                "Message-ID: <l1@b.example>" (coerce '(#\Return #\Newline) 'string)
                (coerce '(#\Return #\Newline) 'string) "b" (coerce '(#\Return #\Newline) 'string))))
; P2-5, P2-6: positional memberships; the conclusion asserted.
(defconst *o1p2-art*
  (fn-make-article "<w1@b.example>" 0 '("fn.test" "fn.letters")
                   '(("fn.test" . 2147483647) ("fn.letters" . 1)) t 0))
; Codex packet-1 F5's countermodel (repeated pairs) is not positional.
(assert-event (not (fn-membership-listp '("fn.test") '(("fn.test" . 1) ("fn.test" . 1)))))
; P2-6 attained exactly at the ten-octet number: " fn.test:2147483647".
(assert-event (equal (len (fn-xref-locations '(("fn.test" . 2147483647)))) 19))

