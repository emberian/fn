; Native calls supply observations, not an ACL2 proof of their C implementation.
(in-package "ACL2")
(include-book "merkle")
(fn2-book-layer :b)

; The primitive boundary includes the two captured input rows, the eight
; uint32 output words (the node message uses little-endian octets), and the digest carrier protected
; while the C call executes. The C/FFI assumption includes no writes to that
; protected carrier. The shared store below is the function raw Lisp calls.
(defun-nx fn2-native-node-reference-observation (dst left right fn2-digests)
 (list :fn2-b3-node
       (fn2-digests-row-snapshot left fn2-digests)
       (fn2-digests-row-snapshot right fn2-digests)
       (fn2-digests-row-snapshot dst (fn2-mk-node dst left right fn2-digests))
       fn2-digests))

(defthm fn2-native-mk-node-whole-effect
 (implies
  (and (fn2-digestsp fn2-digests)
       (fn2-digest-rowp dst fn2-digests)
       (fn2-digest-rowp left fn2-digests)
       (fn2-digest-rowp right fn2-digests)
       (fn2-a-crypto-native
        (fn2-native-node-reference-observation dst left right fn2-digests)
        (list :fn2-b3-node native-left native-right
              (list n0 n1 n2 n3 n4 n5 n6 n7) native-base)))
  (equal (fn2-digest-store-words dst n0 n1 n2 n3 n4 n5 n6 n7 native-base)
         (fn2-mk-node dst left right fn2-digests)))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn2-a-crypto-native-correspondence
                 (reference (fn2-native-node-reference-observation dst left right fn2-digests))
                 (native (list :fn2-b3-node native-left native-right
                               (list n0 n1 n2 n3 n4 n5 n6 n7) native-base)))
                (:instance fn2-mk-node-reconstruct-from-result))
          :in-theory (e/d (fn2-native-node-reference-observation)
                          (fn2-mk-node-reconstruct-from-result)))))

; Three distinct rows: aliased left/right destinations remain meaningful,
; and a live sibling exposes writes that preserve the returned digest.
(defconst *fn2-native-node-witness-digests*
 '((1 9 17) (2 10 18) (3 11 19) (4 12 20)
   (5 13 21) (6 14 22) (7 15 23) (8 16 24) 3))

(defun-nx fn2-native-node-positive-claim (dst)
 (let* ((before *fn2-native-node-witness-digests*)
        (reference (fn2-mk-node dst 0 1 before))
        (words (fn2-digests-row-snapshot dst reference))
        (observation (fn2-native-node-reference-observation dst 0 1 before))
        (after (fn2-digest-store-words dst (nth 0 words) (nth 1 words)
                (nth 2 words) (nth 3 words) (nth 4 words) (nth 5 words)
                (nth 6 words) (nth 7 words) before)))
  (and (fn2-digestsp before)
       (fn2-digest-rowp dst before) (fn2-digest-rowp 0 before) (fn2-digest-rowp 1 before)
       (fn2-a-crypto-native observation observation)
       (equal after reference)
       (equal (fn2-digests-row-snapshot 2 after) '(17 18 19 20 21 22 23 24)))))

(defthm fn2-native-node-positive-left
 (fn2-native-node-positive-claim 0)
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-native-node-positive-claim
                                   fn2-digest-rowp fn2-digests-row-snapshot))))

(defthm fn2-native-node-positive-right
 (fn2-native-node-positive-claim 1)
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-native-node-positive-claim
                                   fn2-digest-rowp fn2-digests-row-snapshot))))

(defun-nx fn2-native-node-frame-mutant-base ()
 (fn2-digest-store-words 2 99 18 19 20 21 22 23 24
                        *fn2-native-node-witness-digests*))

(defun-nx fn2-native-node-frame-mutant-observation ()
 (let* ((before *fn2-native-node-witness-digests*)
        (reference (fn2-mk-node 1 0 1 before)))
  (list :fn2-b3-node (fn2-digests-row-snapshot 0 before)
        (fn2-digests-row-snapshot 1 before)
        (fn2-digests-row-snapshot 1 reference)
        (fn2-native-node-frame-mutant-base))))

(defthm fn2-native-node-frame-assumption-removal
 (let* ((before *fn2-native-node-witness-digests*)
        (reference (fn2-mk-node 1 0 1 before))
        (words (fn2-digests-row-snapshot 1 reference))
        (after (fn2-digest-store-words 1 (nth 0 words) (nth 1 words)
                (nth 2 words) (nth 3 words) (nth 4 words) (nth 5 words)
                (nth 6 words) (nth 7 words) (fn2-native-node-frame-mutant-base))))
  (and (fn2-digestsp before)
       (fn2-digest-rowp 1 before) (fn2-digest-rowp 0 before)
       (fn2-digestsp (fn2-native-node-frame-mutant-base))
       (fn2-digest-rowp 1 (fn2-native-node-frame-mutant-base))
       (equal (fn2-digests-row-snapshot 1 after) words)
       (equal (nth 2 (nth 0 after)) 99)
       (equal (nth 2 (nth 0 reference)) 17)
       (not (equal after reference))
       (not (fn2-a-crypto-native
             (fn2-native-node-reference-observation 1 0 1 before)
             (fn2-native-node-frame-mutant-observation)))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn2-a-crypto-native-correspondence
                 (reference (fn2-native-node-reference-observation
                             1 0 1 *fn2-native-node-witness-digests*))
                 (native (fn2-native-node-frame-mutant-observation))))
          :in-theory (enable fn2-native-node-frame-mutant-base
                 fn2-native-node-frame-mutant-observation
                 fn2-native-node-reference-observation fn2-digest-rowp
                 fn2-digests-row-snapshot))))
