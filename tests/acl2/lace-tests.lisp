; Witnesses and teeth for books/lace.lisp, including the cross-canonical gap
; rebuilt from ~/dev/minidregg/Theory/LaceMerge.lean (`crossCanonical_is_the_gap`,
; `merge_drops_at_collision`, `merge_computes`).
(in-package "ACL2")
(include-book "crypto-seam-tests")
(include-book "../../books/lace-invariants")

(defconst *fn-t-seed-alice* (make-list 32 :initial-element 1))
(defconst *fn-t-seed-bob* (make-list 32 :initial-element 2))
(defconst *fn-t-alice* (make-list 32 :initial-element 17))
(defconst *fn-t-bob* (make-list 32 :initial-element 18))

(defun fn-t-s1 ()
  (fn-stmt-sign *fn-t-seed-alice* *fn-t-alice* 1 1 nil :article
                (fn-record-string-octets "one")))
(defun fn-t-s2 ()
  (fn-stmt-sign *fn-t-seed-alice* *fn-t-alice* 1 2 (list (fn-stmt-id (fn-t-s1)))
                :article (fn-record-string-octets "two")))
(defun fn-t-s3 ()
  (fn-stmt-sign *fn-t-seed-bob* *fn-t-bob* 1 1 (list (fn-stmt-id (fn-t-s1)))
                :article (fn-record-string-octets "three")))

(assert-event (and (fn-stmt-p (fn-t-s1)) (fn-stmt-p (fn-t-s2))
                   (fn-stmt-p (fn-t-s3))))
(assert-event (and (not (equal (fn-stmt-id (fn-t-s1)) (fn-stmt-id (fn-t-s2))))
                   (not (equal (fn-stmt-id (fn-t-s1)) (fn-stmt-id (fn-t-s3))))
                   (not (equal (fn-stmt-id (fn-t-s2)) (fn-stmt-id (fn-t-s3))))))

; -----------------------------------------------------------------------------
; Merge computes (`merge_computes`): the skip guard fires on the shared id.

(defun fn-t-lace-a () (list (fn-t-s1) (fn-t-s2)))
(defun fn-t-lace-b () (list (fn-t-s3) (fn-t-s1)))

(assert-event (fn-lace-p (fn-t-lace-a)))
(assert-event (equal (fn-lace-merge (fn-t-lace-a) (fn-t-lace-b))
                     (list (fn-t-s1) (fn-t-s2) (fn-t-s3))))
(assert-event (equal (fn-lace-merge (fn-t-lace-b) (fn-t-lace-a))
                     (list (fn-t-s3) (fn-t-s1) (fn-t-s2))))
(assert-event (fn-lace-same-idsp (fn-lace-merge (fn-t-lace-a) (fn-t-lace-b))
                                 (fn-lace-merge (fn-t-lace-b) (fn-t-lace-a))))
(assert-event (equal (fn-lace-merge (fn-t-lace-a) (fn-t-lace-a)) (fn-t-lace-a)))
(assert-event (fn-lace-hasp (fn-lace-merge (fn-t-lace-a) (fn-t-lace-b))
                            (fn-stmt-id (fn-t-s3))))
(assert-event (not (fn-lace-hasp (fn-t-lace-a) (fn-stmt-id (fn-t-s3)))))
(assert-event (fn-lace-ids-subsetp (fn-t-lace-a)
                                   (fn-lace-merge (fn-t-lace-a) (fn-t-lace-b))))
; teeth: id-inclusion is not list inclusion, and merged laces are not equal
(assert-event (not (equal (fn-lace-merge (fn-t-lace-a) (fn-t-lace-b))
                          (fn-lace-merge (fn-t-lace-b) (fn-t-lace-a)))))
(assert-event (not (fn-lace-ids-subsetp (fn-t-lace-b) (fn-t-lace-a))))

; Canonicity and lookup on these laces.
(assert-event (fn-lace-canonicalp (fn-t-lace-a)))
(assert-event (fn-lace-cross-canonicalp (fn-t-lace-a) (fn-t-lace-b)))
(assert-event (fn-lace-canonicalp (fn-lace-merge (fn-t-lace-a) (fn-t-lace-b))))
(assert-event (equal (fn-lace-lookup (fn-t-lace-a) (fn-stmt-id (fn-t-s2)))
                     (fn-t-s2)))
(assert-event (equal (fn-lace-lookup (fn-t-lace-a) (fn-stmt-id (fn-t-s3))) nil))
; tooth for same-view: equal ids is a hypothesis
(assert-event (not (equal (fn-lace-lookup (fn-t-lace-a) (fn-stmt-id (fn-t-s3)))
                          (fn-lace-lookup (fn-t-lace-b) (fn-stmt-id (fn-t-s3))))))

; Causal closure.
(assert-event (fn-lace-causally-closedp (fn-t-lace-a)))
(assert-event (not (fn-lace-causally-closedp (list (fn-t-s2)))))
(assert-event (not (fn-lace-causally-closedp (list (fn-t-s3)))))
(assert-event (fn-lace-causally-closedp (fn-lace-merge (fn-t-lace-a) (fn-t-lace-b))))
; tooth: merging an unclosed delta does not make the result closed
(assert-event (not (fn-lace-causally-closedp
                    (fn-lace-merge (list (fn-t-s3))
                                   (list (fn-stmt-sign *fn-t-seed-bob* *fn-t-bob* 1 2
                                                       (list (fn-stmt-id (fn-t-s2)))
                                                       :article '(1)))))))

; -----------------------------------------------------------------------------
; Equivocation: the restore/fork scenario (D10, PRF-017, OBJ-004)

(defun fn-t-fork ()
  (fn-lace-reissue *fn-t-seed-alice* *fn-t-alice* 1 2
                   (fn-record-string-octets "two")
                   (fn-record-string-octets "two, restored")))
(assert-event (not (equal (car (fn-t-fork)) (fn-t-s2))))
(assert-event (fn-lace-same-slotp (car (fn-t-fork)) (fn-t-s2)))
(assert-event (not (equal (car (fn-t-fork)) (cadr (fn-t-fork)))))
(assert-event (not (equal (fn-stmt-id (car (fn-t-fork)))
                          (fn-stmt-id (cadr (fn-t-fork))))))
(assert-event (fn-lace-equivocatorp (fn-lace-merge (fn-t-lace-a)
                                                   (list (cadr (fn-t-fork))))
                                    *fn-t-alice* 1))
(assert-event (fn-lace-equivocatorp (fn-lace-merge (list (car (fn-t-fork)))
                                                   (list (cadr (fn-t-fork))))
                                    *fn-t-alice* 1))
; teeth: one statement alone, an identical reissue, another incarnation,
; another principal, another sequence
(assert-event (not (fn-lace-equivocatorp (fn-t-lace-a) *fn-t-alice* 1)))
(assert-event (not (fn-lace-equivocatorp (fn-lace-merge (fn-t-lace-a)
                                                        (list (fn-t-s2)))
                                         *fn-t-alice* 1)))
(assert-event (not (fn-lace-equivocatorp
                    (fn-lace-merge (fn-t-lace-a)
                                   (list (fn-stmt-sign *fn-t-seed-alice* *fn-t-alice*
                                                       2 2 nil :article '(7))))
                    *fn-t-alice* 1)))
(assert-event (not (fn-lace-equivocatorp (fn-lace-merge (fn-t-lace-a)
                                                        (list (cadr (fn-t-fork))))
                                         *fn-t-bob* 1)))
(assert-event (not (fn-lace-equivocatorp
                    (fn-lace-merge (fn-t-lace-a)
                                   (list (fn-stmt-sign *fn-t-seed-alice* *fn-t-alice*
                                                       1 3 nil :article '(7))))
                    *fn-t-alice* 1)))
; Both forks are retained as evidence, in either merge order.
(assert-event (equal (len (fn-lace-merge (fn-t-lace-a) (list (cadr (fn-t-fork)))))
                     3))
(assert-event (fn-lace-equivocatorp (fn-lace-merge (list (cadr (fn-t-fork)))
                                                   (fn-t-lace-a))
                                    *fn-t-alice* 1))

; -----------------------------------------------------------------------------
; The cross-canonical gap, under a colliding digest.  Every statement with the
; same header LENGTH has the same id here.

(defattach fn-digest fn-toy-length-digest)

(defun fn-t-c1 ()
  (fn-stmt-sign *fn-t-seed-alice* *fn-t-alice* 1 1 nil :article '(1)))
(defun fn-t-c2 ()
  (fn-stmt-sign *fn-t-seed-alice* *fn-t-alice* 1 2 nil :article '(2)))
(assert-event (not (equal (fn-t-c1) (fn-t-c2))))
(assert-event (equal (fn-stmt-id (fn-t-c1)) (fn-stmt-id (fn-t-c2))))

; crossCanonical_is_the_gap: two canonical laces, equal id sets, no
; cross-canonicity, different views.
(assert-event (fn-lace-canonicalp (list (fn-t-c1))))
(assert-event (fn-lace-canonicalp (list (fn-t-c2))))
(assert-event (fn-lace-same-idsp (list (fn-t-c1)) (list (fn-t-c2))))
(assert-event (not (fn-lace-cross-canonicalp (list (fn-t-c1)) (list (fn-t-c2)))))
(assert-event (not (equal (fn-lace-lookup (list (fn-t-c1)) (fn-stmt-id (fn-t-c1)))
                          (fn-lace-lookup (list (fn-t-c2)) (fn-stmt-id (fn-t-c1))))))
; canonical_append_iff: the union is not canonical, exactly because the
; cross term fails.
(assert-event (not (fn-lace-canonicalp (list (fn-t-c1) (fn-t-c2)))))

; merge_drops_at_collision: the merge discards a DIFFERENT statement.
(assert-event (equal (fn-lace-merge (list (fn-t-c1)) (list (fn-t-c2)))
                     (list (fn-t-c1))))
(assert-event (not (member-equal (fn-t-c2)
                                 (fn-lace-merge (list (fn-t-c1)) (list (fn-t-c2))))))

; And the restore/fork is then NOT detectable after a merge: the two forks
; collide, one is dropped, and the equivocation is invisible.  This is the
; A-CRYPTO edge of fn-lace-reissue-detected-after-merge.
(defun fn-t-fork-colliding ()
  (fn-lace-reissue *fn-t-seed-alice* *fn-t-alice* 1 2 '(1) '(2)))
(assert-event (equal (fn-stmt-id (car (fn-t-fork-colliding)))
                     (fn-stmt-id (cadr (fn-t-fork-colliding)))))
(assert-event (not (fn-lace-equivocatorp
                    (fn-lace-merge (list (car (fn-t-fork-colliding)))
                                   (list (cadr (fn-t-fork-colliding))))
                    *fn-t-alice* 1)))
; ... but a lace that HOLDS both (no merge) still shows it.
(assert-event (fn-lace-equivocatorp (fn-t-fork-colliding) *fn-t-alice* 1))

; Same-view without cross-canonicity is not a theorem.
(must-fail
 (thm (implies (fn-lace-same-idsp a b)
               (equal (fn-lace-lookup a h) (fn-lace-lookup b h)))))

(defattach fn-digest fn-toy-mix-digest)
(assert-event (not (equal (fn-stmt-id (fn-t-c1)) (fn-stmt-id (fn-t-c2)))))
(assert-event (fn-lace-cross-canonicalp (list (fn-t-c1)) (list (fn-t-c2))))
