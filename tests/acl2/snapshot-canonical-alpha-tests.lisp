; PRF-1115: canonical history alpha, including the independently held
; composite payload. Physical copy/decoder correspondence remains external.
(in-package "ACL2")
(include-book "../../books/snapshot-canonical-alpha")
(include-book "../../books/codec-attach")
(include-book "snapshot-node-alpha-tests")
(defconst *osac-one*
  (fn-record-make 0 0 0 "<one@example>" '(1 2 3) '("fn.test")
                  "one" "c1" "r1" 1 841000000))
(defconst *osac-two*
  (fn-record-make 1 1 0 "<two@example>" '(4 5) '("fn.test")
                  "two" "c2" "r2" 1 841000001))
(defconst *osac-three*
  (fn-record-make 2 2 0 "<three@example>" '(6 7) '("fn.test")
                  "three" "c3" "r3" 1 841000002))
(defconst *osac-stxa*
  (fn-stxa-make 2 2 0 9 '(112) (fn-record-string-octets "c3")
                (fn-record-encode-impl *osac-three*)
                (fn-stxe-encode
                 (fn-stxe-make 2 2 0 "<three@example>" :unverified
                                *fn-stx-token-signature* 9 '(112)))))
(defun osac-intern-with-orphan ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (let ((fn-arena (fn-arena-seal-list '(99) fn-arena)))
        (fn-intern-events (list *osac-one* *osac-two* *osac-stxa*) nil 9 fn-arena))
      rows)))
(make-event `(defconst *osac-rows* ',(osac-intern-with-orphan)))
(defconst *osac-source* '((99) (1 2 3) (4 5) (6 7)))
(defconst *osac-target* '((1 2 3) (4 5) (6 7)))
(defconst *osac-canonical* (fn-orm-capture *osac-rows* 0))

(defthm osac-canonical-complete-history-alpha-positive-tooth
  (and (fn-orm-rowsp *osac-rows*) (natp 0)
       (equal (len *osac-rows*) 3)
       (fn-held-p (car *osac-rows*))
       (fn-hstxa-p (nth 2 *osac-rows*))
       (not (equal *osac-rows* *osac-canonical*))
       (fn-osa-payload-map-p *osac-rows* 0 *osac-source* *osac-target*)
       (equal (fn-osa-row-alphas *osac-canonical* *osac-target*)
              (fn-osa-row-alphas *osac-rows* *osac-source*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osa-payload-map-p fn-osa-row-alphas
                                     fn-orm-retained-alpha fn-orm-payload-bytes
                                     fn-orm-capture fn-row-bytes))))

; Remove only physical payload correspondence. The changed bytes belong to
; the composite-held ARTICLE, which fn-row-wire-of alone would miss.
(defthm osac-wrong-composite-payload-map-tooth
  (and (fn-orm-rowsp *osac-rows*) (natp 0)
       (not (fn-osa-payload-map-p *osac-rows* 0 *osac-source*
                                 '((1 2 3) (4 5) (88))))
       (not (equal (fn-osa-row-alphas *osac-canonical* '((1 2 3) (4 5) (88)))
                   (fn-osa-row-alphas *osac-rows* *osac-source*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-osa-payload-map-p fn-osa-row-alphas
                                     fn-orm-retained-alpha fn-orm-payload-bytes
                                     fn-orm-capture fn-row-bytes))))

(assert-event
  (and (fn-orm-rowsp *osac-rows*) (natp 0)
       (equal (len (fn-sn-row-verdicts *osac-rows*)) 3)
       (equal (fn-sn-index-fold *osac-canonical* (fn-stx-index-empty))
              (fn-sn-index-fold *osac-rows* (fn-stx-index-empty)))
       (equal (fn-sn-row-verdicts-fold *osac-canonical* nil)
              (fn-sn-row-verdicts-fold *osac-rows* nil)))
)
