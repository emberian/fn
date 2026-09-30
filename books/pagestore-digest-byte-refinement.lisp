;; Exact byte-tail algorithm correspondence; proof-only spans stay logical.
(in-package "ACL2")
(include-book "pagestore-digest-byte-cursor")
(include-book "pagestore-digest-cursor-refinement")
(local (include-book "arithmetic/top" :dir :system))

(defthm pgs-dbr-span-length
  (implies (and (natp pos) (natp end) (<= pos end)
                (<= (* 8 pos) (len msg)) (<= (len msg) (* 8 end)))
           (equal (len (pgs-dcr-span pos end msg)) (- (len msg) (* 8 pos))))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-span) (fn-b3-firstn fn-b3-nthcdrx)))))

(defthm pgs-dbr-chunk-tail-model-last
  (implies (and (natp pos) (natp end) (<= pos end) (<= (- end pos) 8)
                (<= (* 8 pos) (len msg)) (<= (len msg) (* 8 end))
                (true-listp cv) (equal (len cv) 8))
           (equal (fn-b3-chunk cv (pgs-dcr-span pos end msg) counter 0 startp)
                  (fn-b3-output cv (fn-b3-words 16 (pgs-dcr-span pos end msg))
                                counter (- (len msg) (* 8 pos))
                                (logior (if startp 1 0) 2))))
  :hints (("Goal" :expand ((fn-b3-chunk cv (pgs-dcr-span pos end msg) counter 0 startp))
                  :in-theory (e/d (fn-b3-output)
                                   (pgs-dcr-span fn-b3-chunk fn-b3-compress fn-b3-cv8)))))

(local
 (defthm pgs-dbr-firstn-after-source-end
   (implies (<= (len msg) (nfix offset))
            (equal (fn-b3-firstn count (fn-b3-nthcdrx offset msg)) nil))
   :hints (("Goal" :induct (fn-b3-nthcdrx offset msg)
                   :in-theory (enable fn-b3-firstn fn-b3-nthcdrx)))))

(defthm pgs-dbr-span-at-source-end-empty
  (implies (<= (len msg) (* 8 (nfix pos)))
           (equal (pgs-dcr-span pos end msg) nil))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-span) (fn-b3-firstn fn-b3-nthcdrx)))))

(defthm pgs-dbr-chunk-tail-keeps-current-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :chunk)
                (natp byte-total) (equal (len msg) byte-total)
                (natp (pgs-dc-start pgs-digest))
                (natp (pgs-dc-pos pgs-digest)) (natp (pgs-dc-end pgs-digest))
                (<= (pgs-dc-start pgs-digest) (pgs-dc-pos pgs-digest))
                (<= (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest))
                (<= (* 8 (pgs-dc-pos pgs-digest)) byte-total)
                (<= byte-total (* 8 (pgs-dc-end pgs-digest)))
                (equal (pgs-dc-end pgs-digest) (pgs-dc-total pgs-digest))
                (<= (- (pgs-dc-end pgs-digest) (pgs-dc-pos pgs-digest)) 8)
                (true-listp (pgs-dc-cv pgs-digest)) (equal (len (pgs-dc-cv pgs-digest)) 8)
                (equal block (fn-b3-words 16 (pgs-dcr-span (pgs-dc-pos pgs-digest)
                                                               (pgs-dc-end pgs-digest) msg))))
           (equal (pgs-dcr-current msg (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest)))
                  (pgs-dcr-current msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-current pgs-dcb-step fn-b3-output)
                                   (nth update-nth pgs-dcr-span fn-b3-chunk fn-b3-node
                                        pgs-dc-pad-block fn-b3-cv8))
                  :do-not-induct t)))

(defthm pgs-dbr-tail-depth-unfolds
  (implies (and (equal (pgs-dc-mode pgs-digest) :chunk)
                (equal (pgs-dc-end pgs-digest) (pgs-dc-total pgs-digest))
                (<= (- (pgs-dc-end pgs-digest) (pgs-dc-pos pgs-digest)) 8))
           (equal (pgs-dc-depth (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest)))
                  (pgs-dc-depth pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcb-step) (nth update-nth)))))

(defthm pgs-dbr-tail-fold-unfolds
  (implies (and (equal (pgs-dc-mode pgs-digest) :chunk)
                (equal (pgs-dc-end pgs-digest) (pgs-dc-total pgs-digest))
                (<= (- (pgs-dc-end pgs-digest) (pgs-dc-pos pgs-digest)) 8))
           (equal (pgs-dcr-fold depth out msg (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest)))
                  (pgs-dcr-fold depth out msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcb-step) (nth update-nth pgs-dcr-fold)))))

(defthm pgs-dbr-chunk-tail-preserves-denotation
  (implies (and (equal (pgs-dc-mode pgs-digest) :chunk)
                (natp byte-total) (equal (len msg) byte-total)
                (natp (pgs-dc-start pgs-digest))
                (natp (pgs-dc-pos pgs-digest)) (natp (pgs-dc-end pgs-digest))
                (<= (pgs-dc-start pgs-digest) (pgs-dc-pos pgs-digest))
                (<= (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest))
                (<= (* 8 (pgs-dc-pos pgs-digest)) byte-total)
                (<= byte-total (* 8 (pgs-dc-end pgs-digest)))
                (equal (pgs-dc-end pgs-digest) (pgs-dc-total pgs-digest))
                (<= (- (pgs-dc-end pgs-digest) (pgs-dc-pos pgs-digest)) 8)
                (true-listp (pgs-dc-cv pgs-digest)) (equal (len (pgs-dc-cv pgs-digest)) 8)
                (equal block (fn-b3-words 16 (pgs-dcr-span (pgs-dc-pos pgs-digest)
                                                               (pgs-dc-end pgs-digest) msg))))
           (equal (pgs-dcr-denote msg (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest)))
                  (pgs-dcr-denote msg pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcr-denote)
                                   (nth update-nth pgs-dcr-current pgs-dcr-fold pgs-dcb-step)))))

(defthm pgs-dbr-byte-tail-boundary-refines-page-step
  (implies (and (natp (pgs-dc-pos pgs-digest)) (natp (pgs-dc-end pgs-digest))
                (<= (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest))
                (equal byte-total (* 8 (pgs-dc-total pgs-digest))))
           (equal (pgs-dcb-step byte-total block pgs-digest)
                  (pgs-dc-step block pgs-digest)))
  :hints (("Goal" :in-theory (e/d (pgs-dcb-step pgs-dc-step)
                                   (nth update-nth fn-b3-output pgs-dc-pad-block fn-b3-output-cv))
                  :do-not-induct t)))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
(defthm pgs-dbr-word-count-covers-byte-total
  (implies (natp byte-total)
           (<= byte-total (* 8 (pgs-dcb-word-count byte-total))))
  :hints (("Goal" :in-theory (e/d (pgs-dcb-word-count) (ceiling))))
  :rule-classes (:rewrite :linear))
)

(local
 (defthm pgs-dbr-firstn-long-identity
   (implies (and (true-listp msg) (<= (len msg) (nfix count)))
            (equal (fn-b3-firstn count msg) msg))
   :hints (("Goal" :induct (fn-b3-firstn count msg)
                   :in-theory (enable fn-b3-firstn)))))

(defthm pgs-dbr-byte-begin-denotation-is-node
  (implies (and (natp byte-total) (true-listp msg) (equal (len msg) byte-total))
           (equal (pgs-dcr-denote msg
                    (pgs-dcb-begin sel base byte-total capture lease pgs-digest))
                  (fn-b3-node *fn-b3-iv* msg 0 0)))
  :hints (("Goal" :expand ((fn-b3-nthcdrx 0 msg))
                  :in-theory (e/d (pgs-dcr-denote pgs-dcr-current pgs-dcb-begin pgs-dc-begin
                                                  pgs-dcr-fold pgs-dcr-span)
                                   (nth update-nth fn-b3-node fn-b3-firstn fn-b3-nthcdrx
                                        pgs-dcb-word-count)))))

(local
 (defthm pgs-dbr-octet-listp-true-listp
   (implies (fn-b3-octet-listp msg) (true-listp msg))
   :hints (("Goal" :induct (fn-b3-octet-listp msg)
                   :in-theory (enable fn-b3-octet-listp)))))

(defthm pgs-dbr-byte-initial-root-is-blake3
  (implies (and (natp byte-total) (fn-b3-octet-listp msg) (equal (len msg) byte-total))
           (equal (fn-b3-output-root
                    (pgs-dcr-denote msg
                      (pgs-dcb-begin sel base byte-total capture lease pgs-digest)))
                  (fn-blake3 msg)))
  :hints (("Goal" :in-theory (e/d (fn-blake3 fn-b3-hash)
                                   (pgs-dcr-denote pgs-dcb-begin fn-b3-output-root
                                        fn-b3-node fn-b3-fix-octets)))))

;; Exact arbitrary-byte terminal boundary, conditional on the carried
;; captured-source denotation. This does not establish a trajectory invariant.
(defthm pgs-dbr-byte-terminal-octets-is-blake3
  (implies
    (and (natp byte-total) (fn-b3-octet-listp msg) (equal (len msg) byte-total)
         (equal (pgs-dc-mode pgs-digest) :root) (equal (pgs-dc-depth pgs-digest) 0)
         (equal (pgs-dcr-denote msg pgs-digest)
                (pgs-dcr-denote msg
                  (pgs-dcb-begin sel base byte-total capture lease pgs-digest))))
    (equal (pgs-dcb-result-octets
             (mv-nth 1 (pgs-dcb-step byte-total nil pgs-digest)))
           (fn-blake3 msg)))
  :hints (("Goal" :in-theory (e/d (pgs-dcb-result-octets pgs-dcb-step pgs-dc-step
                                                  pgs-dcr-denote pgs-dcr-current pgs-dcr-fold
                                                  fn-blake3 fn-b3-hash)
                                   (nth update-nth pgs-dcb-begin fn-b3-output-root fn-b3-node
                                        fn-b3-fix-octets))))
  :rule-classes nil)

(defthm pgs-dbr-final-descriptor-byte-count-is-bounded
  (implies (and (natp byte-total) (equal (pgs-dc-mode pgs-digest) :chunk)
                (natp (pgs-dc-pos pgs-digest)) (natp (pgs-dc-end pgs-digest))
                (equal (pgs-dc-total pgs-digest) (pgs-dcb-word-count byte-total))
                (equal (pgs-dc-end pgs-digest) (pgs-dc-total pgs-digest))
                (<= (* 8 (pgs-dc-pos pgs-digest)) byte-total)
                (<= (- (pgs-dc-end pgs-digest) (pgs-dc-pos pgs-digest)) 8))
           (let ((count (fn-b3-nthx 3 (pgs-dc-output
                            (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest))))))
             (and (natp count) (<= count 64))))
  :hints (("Goal" :use pgs-dbr-word-count-covers-byte-total
                  :in-theory (e/d (pgs-dcb-step fn-b3-output fn-b3-nthx)
                                   (nth update-nth pgs-dc-pad-block pgs-dcb-word-count)))))
