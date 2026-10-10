; Witnesses and teeth for books/filed-groups (O1 packets 1 and 2): each keystone's
; antecedent satisfied on a concrete article, the invariant refusing groups
; its header does not name, and the signed constructor's fixture
; (tests/acl2/hybrid-store-tests.lisp) satisfying SIGNED with the invariant.
(in-package "ACL2")
(include-book "../../books/filed-groups")
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
(assert-event (equal (fn-o1-source-newsgroups *o1-src*)
                     (list (fn-record-string-octets "fn.test") (fn-record-string-octets "fn.letters"))))
; satisfiable: the whole list, a sublist, the empty list
(assert-event (fn-o1-filed-within-sourcep '("fn.test" "fn.letters") *o1-src*))
(assert-event (fn-o1-filed-within-sourcep '("fn.letters") *o1-src*))
; teeth: a group the header does not name; the right groups out of order; a duplicate
(assert-event (not (fn-o1-filed-within-sourcep '("fn.other") *o1-src*)))
(assert-event (not (fn-o1-filed-within-sourcep '("fn.letters" "fn.test") *o1-src*)))
(assert-event (not (fn-o1-filed-within-sourcep '("fn.test" "fn.test") *o1-src*)))
; control: filed in its filing group.  The invariant is a size predicate: it
; also admits a control article's Newsgroups names (Codex F7), and says
; nothing of exclusive control filing or malformed-control refusal.
(assert-event (fn-o1-control-filedp '("control.cancel") *o1-ctl*))
(assert-event (fn-o1-filed-within-sourcep '("control.cancel") *o1-ctl*))
(assert-event (not (fn-o1-control-filedp '("control") *o1-ctl*)))
; the signed binding the keystone reads: groups as hybrid-store computes them
(assert-event (equal (fn-hsig-source-filed-groups *o1-src* (fn-hsig-authored-source-fields *o1-src*))
                     '("fn.test" "fn.letters")))
(assert-event (equal (fn-hsig-source-filed-groups *o1-ctl* (fn-hsig-authored-source-fields *o1-ctl*))
                     '("control.cancel")))
; Codex F2: the SIGNED antecedent satisfied, with the invariant, on the
; existing fixture (tests/acl2/hybrid-store-tests.lisp:303); and its teeth:
; the same event with groups outside the source's Newsgroups is refused.
(assert-event
 (and (fn-hsig-authorized-submission-event
       2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
       *hst-authored-source* '("example") "obligation" "subject" "release"
       (fn-charge-for-payload (len *hst-authored-source*))
       *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
       :verified :verified (fn-clock-observation 1 841000000000 0 t))
      (fn-o1-filed-within-sourcep '("example") *hst-authored-source*)))
(assert-event
 (and (not (fn-hsig-authorized-submission-event
            2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
            *hst-authored-source* '("other") "obligation" "subject" "release"
            (fn-charge-for-payload (len *hst-authored-source*))
            *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
            :verified :verified (fn-clock-observation 1 841000000000 0 t)))
      (not (fn-o1-filed-within-sourcep '("other") *hst-authored-source*))))
; empty list; the NAMES and SUBSEQ inequalities instantiated; CONTROL at 19
(assert-event (fn-o1-filed-within-sourcep nil *o1-src*))
(assert-event (let ((names (fn-o1-source-newsgroups *o1-src*)))
                (and (equal (fn-o1-octet-sum names) 17) (equal (len names) 2)
                     (<= (+ (fn-o1-octet-sum names) (len names)) (+ 1 (len (fn-record-string-octets " fn.test,fn.letters")))))))
(assert-event (equal (len (fn-record-string-octets (fn-ctl-filing-group (fn-record-string-octets "checkgroups")))) 19))

; ---------------------------------------------------------------------------
; Packet 2.  Each keystone's whole implication on a concrete instance (its
; antecedent and its conclusion), and for the bounds a hypothesis-removal
; tooth: the hypothesis dropped, the other one kept, the conclusion false.
(defconst *o1p2-lim* (fn-article-limits 100 200 16384))
(defconst *o1p2-zero* (fn-article-limits 100 200 0))

; P2-1/P2-2: the native injected event exists, files within its source and
; within the RECEIVED payload it stores; a group the received header does
; not name is outside the invariant and the constructor refuses it.
(assert-event (and *hst-injected-event*
                   (fn-o1-filed-within-sourcep '("example") *hst-authored-source*)
                   (fn-o1-filed-within-sourcep '("example") *hst-injected-received*)))
(assert-event (not (fn-o1-filed-within-sourcep '("other") *hst-injected-received*)))
(assert-event (null (fn-hsig-authorized-injected-carried-submission-event
                     2 3 4 4 *hst-snapshot* "<hybrid@example.invalid>"
                     *hst-authored-source* *hst-injected-received* '("other")
                     *hst-injected-obligation* *hst-injected-subject* "release"
                     (fn-charge-for-payload (len *hst-injected-received*))
                     *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
                     :verified :verified *hst-injection-config*
                     *hst-injection-observation*)))
; P2-3: the peer event exists and files within the relayed payload.
(assert-event (and *pat-event* (fn-o1-filed-within-sourcep '("fn.test") *pat-relayed*)))
(assert-event (not (fn-o1-filed-within-sourcep '("fn.other") *pat-relayed*)))

; P2-4, the multi-name branch: both hypotheses and the header-charge
; conclusion (17 + 2 <= 16385); tooth: drop the parse hypothesis (limit 0),
; containment still holds and the conclusion fails (19 > 1, not a singleton).
(assert-event (let ((g '("fn.test" "fn.letters")))
                (and (fn-article-result-okp (fn-article-parse-under *o1-src* *o1p2-lim*))
                     (fn-o1-filed-within-sourcep g *o1-src*)
                     (<= (+ (fn-o1-octet-sum (fn-o1-groups-octets g)) (len g))
                         (+ 1 (fn-article-limit-octets *o1p2-lim*))))))
(assert-event (let ((g '("fn.test" "fn.letters")))
                (and (not (fn-article-result-okp (fn-article-parse-under *o1-src* *o1p2-zero*)))
                     (fn-o1-filed-within-sourcep g *o1-src*)
                     (not (<= (+ (fn-o1-octet-sum (fn-o1-groups-octets g)) (len g))
                              (+ 1 (fn-article-limit-octets *o1p2-zero*)))))))
; P2-4 with a singleton longer than 19 octets at its own tightest limits:
; the bound comes from the header-charge disjunct, not the shortcut.
(defconst *o1p2-long*
  (fn-record-string-octets
   (concatenate 'string "From: a@b.example" (coerce '(#\Return #\Newline) 'string)
                "Newsgroups: comp.lang.lisp.franz.extra" (coerce '(#\Return #\Newline) 'string)
                "Subject: s" (coerce '(#\Return #\Newline) 'string)
                "Message-ID: <l1@b.example>" (coerce '(#\Return #\Newline) 'string)
                (coerce '(#\Return #\Newline) 'string) "b" (coerce '(#\Return #\Newline) 'string))))
(assert-event (let* ((g '("comp.lang.lisp.franz.extra"))
                     (lim (fn-article-header-census *o1p2-long*)))
                (and (fn-article-result-okp (fn-article-parse-under *o1p2-long* lim))
                     (fn-o1-filed-within-sourcep g *o1p2-long*)
                     (< 19 (len (fn-record-string-octets (car g))))
                     (<= (+ (fn-o1-octet-sum (fn-o1-groups-octets g)) (len g))
                         (+ 1 (fn-article-limit-octets lim))))))

; P2-5, P2-6: positional memberships; the conclusion asserted.
(defconst *o1p2-art*
  (fn-make-article "<w1@b.example>" 0 '("fn.test" "fn.letters")
                   '(("fn.test" . 2147483647) ("fn.letters" . 1)) t 0))
(assert-event (and (fn-membership-listp (fn-article-groups *o1p2-art*) (fn-article-memberships *o1p2-art*))
                   (fn-o1-subseqp (fn-o1-groups-octets
                                   (fn-o1-pair-names (fn-xref-pairs-of (fn-article-memberships *o1p2-art*) *o1p2-art*)))
                                  (fn-o1-groups-octets (fn-article-groups *o1p2-art*)))))
; Codex packet-1 F5's countermodel (repeated pairs) is not positional.
(assert-event (not (fn-membership-listp '("fn.test") '(("fn.test" . 1) ("fn.test" . 1)))))
; P2-6 attained exactly at the ten-octet number: " fn.test:2147483647".
(assert-event (equal (len (fn-xref-locations '(("fn.test" . 2147483647)))) 19))

; P2-7 over a real arena (*o1-src* sealed as the article's handle): the
; antecedent and the bound (32 <= 196620); tooth: drop the parse hypothesis
; (limit 0), the invariant still holds and 32 > max(31, 12).
(defun o1p2-x (payloads article limits)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let ((fn-arena (fn-arn-seal-many payloads fn-arena)))
        (let ((p (fn-nntp-article-bytes article fn-arena)))
          (mv (list (fn-article-result-okp (fn-article-parse-under p limits))
                    (fn-o1-article-within-headerp article p)
                    (len (fn-xref-locations (fn-xref-pairs article))))
              fn-arena)))
      r)))
(assert-event (let ((r (o1p2-x (list *o1-src*) *o1p2-art* *o1p2-lim*)))
                (and (car r) (cadr r) (equal (caddr r) 32)
                     (<= (caddr r) (max 31 (* 12 (+ 1 (fn-article-limit-octets *o1p2-lim*))))))))
(assert-event (let ((r (o1p2-x (list *o1-src*) *o1p2-art* *o1p2-zero*)))
                (and (not (car r)) (cadr r)
                     (not (<= (caddr r) (max 31 (* 12 (+ 1 (fn-article-limit-octets *o1p2-zero*)))))))))
