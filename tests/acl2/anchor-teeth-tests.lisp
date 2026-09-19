; Teeth for the monotone-anchor rule.
;
; One `must-fail' case per hypothesis of each keystone in
; books/anchor-invariants.lisp.  A hypothesis that can be dropped and still
; leave the theorem provable was not doing any work; each case below shows the
; conclusion does not survive without it.

(in-package "ACL2")

(include-book "../../books/anchor-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; fn-anchor-accepted-anchor-is-strictly-newer
;
; Hypotheses: the node holds an anchor already, and the outcome is `:accepted'.

; Without "the node holds an anchor", a node with no anchor accepts its first
; response, and there is nothing for it to be newer than.
(must-fail
 (defthm teeth-accepted-newer-needs-a-held-anchor
   (implies (and (fn-anchor-nodep node)
                 (equal (fn-anchor-status (fn-anchor-node-accept node a))
                        :accepted))
            (fn-anchor-newerp a (fn-anchor-node-latest node)))))

; Without "the outcome is accepted", a refused stale response would have to be
; newer than the anchor it failed to outdate.
(must-fail
 (defthm teeth-accepted-newer-needs-acceptance
   (implies (and (fn-anchor-nodep node)
                 (fn-anchor-node-latest node))
            (fn-anchor-newerp a (fn-anchor-node-latest node)))))

; -----------------------------------------------------------------------------
; fn-anchor-restore-refuses-image-it-cannot-outdate
;
; Hypotheses: the image refers to an anchor, and the presented anchor does not
; outdate it.

; Without "the image refers to an anchor", an image carrying no freshness
; evidence at all would be refused, which would make every first restore
; impossible.
(must-fail
 (defthm teeth-restore-refusal-needs-a-referenced-anchor
   (implies (and (fn-anchor-imagep image)
                 (not (fn-anchor-newerp presented
                                        (fn-anchor-image-referenced image))))
            (not (equal (fn-anchor-status
                         (fn-anchor-restore node image presented))
                        :accepted)))))

; Without "the presented anchor does not outdate it", a genuinely fresh
; restore would be refused.
(must-fail
 (defthm teeth-restore-refusal-needs-a-non-outdating-anchor
   (implies (and (fn-anchor-imagep image)
                 (fn-anchor-image-referenced image))
            (not (equal (fn-anchor-status
                         (fn-anchor-restore node image presented))
                        :accepted)))))

; -----------------------------------------------------------------------------
; fn-anchor-accepted-restore-outdates-the-image
;
; Without "the outcome is accepted", a refusal would carry the same conclusion
; the acceptance does.
(must-fail
 (defthm teeth-accepted-restore-conclusion-needs-acceptance
   (implies (and (fn-anchor-imagep image)
                 (fn-anchor-image-referenced image))
            (fn-anchor-newerp presented (fn-anchor-image-referenced image)))))

; -----------------------------------------------------------------------------
; fn-anchor-incarnation-advances-only-under-a-newer-anchor
;
; Without "the node holds an anchor", a node with none advances on its first
; response and the conclusion is false.
(must-fail
 (defthm teeth-advance-needs-a-held-anchor
   (implies (and (fn-anchor-nodep node)
                 (not (equal (fn-anchor-node-incarnation
                              (fn-anchor-payload (fn-anchor-node-advance node a)))
                             (fn-anchor-node-incarnation node))))
            (fn-anchor-newerp a (fn-anchor-node-latest node)))))

; -----------------------------------------------------------------------------
; fn-anchor-fork-admits-neither-image
;
; Hypotheses: the incarnations agree, and the referenced anchors differ.

; Without "the incarnations agree", two ordinary successive incarnations of
; one origin would be reported as a fork.
(must-fail
 (defthm teeth-fork-needs-equal-incarnations
   (implies (not (equal (fn-anchor-image-referenced left)
                        (fn-anchor-image-referenced right)))
            (equal (fn-anchor-status (fn-anchor-pair-admit left right))
                   :refused))))

; Without "the referenced anchors differ", one image seen twice would be a
; fork, and no restore could ever be readmitted.
(must-fail
 (defthm teeth-fork-needs-differing-anchors
   (implies (equal (fn-anchor-image-incarnation left)
                   (fn-anchor-image-incarnation right))
            (equal (fn-anchor-status (fn-anchor-pair-admit left right))
                   :refused))))

; -----------------------------------------------------------------------------
; fn-anchor-restore-observed-is-restore
;
; Without "the host verdict is the seam's value for this anchor", the host
; entry and the theorems' subject come apart: a host that answers `t' to
; everything is not computing `fn-anchor-verifiedp'.
(must-fail
 (defthm teeth-observed-restore-needs-the-verdict
   (equal (fn-anchor-restore-observed node image presented verdict)
          (fn-anchor-restore node image presented))))

; -----------------------------------------------------------------------------
; The crypto seam's own constraints
;
; `fn-anchor-sig-verify' is constrained to refuse a key or signature of the
; wrong width.  Nothing constrains it to refuse anything else, and in
; particular unforgeability is not available: this is the case that fails.
(must-fail
 (defthm teeth-sig-verify-is-not-unforgeable
   (implies (and (fn-anchor-p a) (fn-anchor-p b)
                 (not (equal (fn-anchor-signed-octets a)
                             (fn-anchor-signed-octets b))))
            (not (and (fn-anchor-verifiedp a) (fn-anchor-verifiedp b))))))

; And the constraint that does hold has teeth: a 63-octet signature never
; verifies, so a truncated response cannot be accepted.
(defthm teeth-truncated-signature-never-verifies
  (implies (not (fn-anchor-octets-of-lengthp signature *fn-anchor-sig-octets*))
           (not (fn-anchor-sig-verify key message signature))))
