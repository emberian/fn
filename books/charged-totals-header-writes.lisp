; fn: the charged-totals header's writer runs, admitted (Builder A, lane
; vertical, 2026-10-10; statement packet build/vertical-runs/ct2/packet-v31.md
; v3.3; proofs: Codex round 6, build/vertical-runs/codex/review-ct2/r6-k8a.lsp
; and r6-k8t.lsp, each helper local).
;
; KEYSTONES (the packet's statements verbatim, :rule-classes nil)
;   K8a fn-cth-arena-write-is-admitted: the arena run a write ends :ok from a
;       carried total T0 is admitted by the reader from T0, to T0 plus the
;       octets written.  Domain (rule 6b-1): the arena stobj's recognizer,
;       the write step's source guard, the run's chunk width, and the payload
;       count within the head's length field (Codex rounds 4 and 5).
;   K8t fn-cth-table-write-is-admitted: the four tables the publication
;       setup writes from a carried total T1 are admitted by the reader from
;       T1, to T1 plus the octets written (the programs within the u64
;       length field, Codex round 4).
; With K8c (books/charged-totals-header.lisp) the whole file's admission is
; the writer's (K7's premise).  The host: host/native/io.lisp
; fnn-checkpoint-write-steps starts the arena run at the header's total and
; the tables at the octets written since the header.
;
; Its own book: the proofs were found over the packet's world (the
; definitions and the includes below, none of the header book's local
; lemmas), whose rewriter they are tuned to.

(in-package "ACL2")
(include-book "charged-totals-header")
(include-book "records-attach")
(include-book "catalog-record")
(include-book "store-checkpoint-arena-load")

; K8a (proof: Codex round 6, review-ct2/r6-k8a.lsp, helpers local).
(encapsulate ()
(local
 (include-book "arithmetic/top" :dir :system))
(local
 (in-theory (disable fn-sccr-cbor-octet-listp-is-scc-octet-listp
                    fn-sccr-scc-octet-listp-is-cbor-octet-listp
                    fn-oct-bufp-true-listp fn-octets$c-bufp)))
(local
 (defthm r6-u64-true (true-listp (fn-scc-u64 n k))))
(local
 (defthm r6-header-shape
 (and (true-listp (fn-scc-header i c l s))
      (equal (len (fn-scc-header i c l s)) 37)
      (fn-scc-octet-listp (fn-scc-header i c l s)))
 :hints (("Goal" :in-theory (e/d (fn-scc-header fn-scc-octetp) (fn-scc-u64))))))
(local
 (defthm r6-take-append
 (implies (and (true-listp a) (natp k) (<= k (len a)))
          (equal (take k (append a b)) (take k a)))))
(local
 (defthm r6-drop-append
 (implies (equal k (len a)) (equal (nthcdr k (append a b)) b))))
(local
 (defthm r6-long-len
 (implies (natp k) (equal (fn-scc-long-enoughp k a) (<= k (len a))))))
(local
 (defthm r6-octets-append
 (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
          (fn-scc-octet-listp (append a b)))
 :hints (("Goal" :induct (fn-scc-octet-listp a)
                 :in-theory (e/d (fn-scc-octet-listp) (fn-scc-octet-listp-facts))))))
(local
 (defthm r6-take-all
 (implies (and (true-listp x) (equal k (len x))) (equal (take k x) x))))
(local
 (defthm r6-u64-value
 (implies (and (natp n) (natp k) (< n (expt 256 k)))
          (equal (fn-scc-le-value (fn-scc-u64 n k)) n))
 :hints (("Goal" :induct (fn-scc-u64 n k)))))
(local
 (defthm r6-u64-read
 (implies (and (natp n) (< n *fn-scc-u64-bound*))
          (equal (fn-scc-u64-at (append (fn-scc-u64 n 8) rest)) n))
 :hints (("Goal" :in-theory (e/d (fn-scc-u64-at) (fn-scc-u64))))))
(local
 (defthm r6-header-admit
 (implies (and (natp l) (< l *fn-scc-u64-bound*))
  (equal (fn-sccr-admit-segment (fn-scc-header i c l s) total sb fb)
         (if (and (natp total) (natp sb) (natp fb)
                  (<= (+ 69 l) sb) (<= (+ total 69 l) fb))
             (list :ok (+ 69 l) l) (list :refused :exceeds-bound))))
 :hints (("Goal" :do-not-induct t :use ((:instance r6-header-shape))
          :in-theory (e/d (fn-sccr-admit-segment fn-scc-header fn-scc-parse-header fn-scc-u64-at)
                          (fn-scc-u64 fn-scc-le-value r6-header-shape))))))
(local
 (defthm r6-seal-facts
 (implies (and (fn-scc-octet-listp prev) (fn-scc-octet-listp header) (fn-scc-octet-listp chunk))
  (and (fn-scc-octet-listp (fn-scc-seal prev header chunk))
       (true-listp (fn-scc-seal prev header chunk))
       (equal (len (fn-scc-seal prev header chunk)) 32)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-frame-trailer-is-a-digest (octets (append prev header chunk))))
          :in-theory (e/d (fn-scc-seal fn-frame-digestp)
                          (fn-frame-trailer-is-a-digest))))))
(local
 (defthm r6-nth-append
 (implies (and (natp n) (< n (len a)))
          (equal (nth n (append a b)) (nth n a)))))
(local
 (defthm r6-admit-header-append
 (implies (and (fn-scc-octet-listp header) (equal (len header) 37)
               (fn-scc-octet-listp rest))
  (equal (fn-sccr-admit-segment (append header rest) total sb fb)
         (fn-sccr-admit-segment header total sb fb)))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-sccr-admit-segment fn-sccr-parse-header-of-append fn-sccr-other-schemap)
                          (fn-scc-parse-header fn-scc-octet-listp))))))
(local
 (defthm r6-frame-admission
 (implies (and (fn-scc-octet-listp chunk) (fn-scc-octet-listp prev)
               (< (len chunk) *fn-scc-u64-bound*))
  (equal (fn-sccr-admit-segment
           (append (fn-scc-header i c (len chunk) s) chunk
                   (fn-scc-seal prev (fn-scc-header i c (len chunk) s) chunk)) total sb fb)
         (fn-sccr-admit-segment (fn-scc-header i c (len chunk) s) total sb fb)))
 :hints (("Goal" :in-theory (union-theories
           '(r6-admit-header-append r6-header-shape r6-octets-append r6-seal-facts)
           (theory 'minimal-theory))))))
(local
 (defthm r6-frame-length
 (implies (and (fn-scc-octet-listp chunk) (fn-scc-octet-listp prev))
  (equal (len (append (fn-scc-header i c (len chunk) s) chunk
                     (fn-scc-seal prev (fn-scc-header i c (len chunk) s) chunk)))
         (+ 69 (len chunk))))
 :hints (("Goal" :in-theory (e/d () (fn-scc-header fn-scc-seal fn-scc-octet-listp))))))
(local
 (defthm r6-head-octets
 (implies (fn-scc-nat-encodablep n) (fn-scc-octet-listp (fn-scka-head n)))
 :hints (("Goal" :in-theory (e/d (fn-scka-head fn-scc-nat-octets fn-scc-nat-encodablep fn-scc-octet-listp fn-scc-octetp)
                                  (fn-scc-le-digits))))))
(local
 (defthm r6-body-octets
 (implies (and (fn-arena-p fn-arena) (fn-scka-srcs-okp srcs fn-arena)
               (natp k) (<= k (len srcs)))
          (fn-scc-octet-listp (fn-scka-body (take k (fn-scka-src-payloads srcs fn-arena)))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-scka-append-batch-is-body (fn-octets nil))
                (:instance fn-scka-append-batch-octets-p (fn-octets nil)))
          :in-theory (e/d (fn-oct-octets-p-is-octet-listp fn-sccr-cbor-octet-listp-is-scc-octet-listp)
                          (fn-scka-body fn-scka-srcs-okp fn-scka-src-payloads fn-scka-append-batch
                           fn-scka-append-batch-is-body fn-scka-append-batch-octets-p))))))
(local
 (defthm r6-last-frame
 (implies (true-listp fn-octets)
  (equal (fn-ockp-last-frame 0 i c s prev fn-octets)
         (list (list (fn-scc-header i c (len fn-octets) s) 0 (len fn-octets)
                     (fn-scc-seal prev (fn-scc-header i c (len fn-octets) s) fn-octets)))))
 :hints (("Goal" :in-theory (e/d (fn-ockp-last-frame fn-sccb-slice-acc-is-slice-list)
                                  (fn-scc-header fn-scc-seal))))))
(local
 (defthm r6-admit-single-header
 (implies (and (natp l) (< l *fn-scc-u64-bound*)
               (equal (car (fn-ockp-admit-frames
                             (list (list (fn-scc-header i c l s) a b trailer)) total sb fb)) :ok))
  (and (equal (fn-sccr-admit-segment (fn-scc-header i c l s) total sb fb)
              (list :ok (+ 69 l) l))
       (equal (nth 1 (fn-ockp-admit-frames
                       (list (list (fn-scc-header i c l s) a b trailer)) total sb fb))
              (+ total 69 l))
       (natp total)))
 :hints (("Goal" :in-theory (union-theories
                '(fn-ockp-admit-frames r6-header-admit natp nth nfix zp car-cons cdr-cons)
                (theory 'minimal-theory))))))
(local
 (defthm r6-batch-buffer
 (implies (and (posp (nth 0 pst))
               (<= (nfix (car (nth 2 pst))) (len (fn-scka-src-payloads (nth 1 pst) fn-arena))))
  (equal (mv-nth 3 (fn-scka-write-step pst n count s sb fb fn-arena fn-octets))
         (fn-scka-body (take (nfix (car (nth 2 pst))) (fn-scka-src-payloads (nth 1 pst) fn-arena)))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-scka-append-batch-is-body (srcs (nth 1 pst))
                           (k (nfix (car (nth 2 pst)))) (fn-octets nil)))
          :in-theory (e/d (fn-scka-write-step fn-oct-append-list-is-append)
                          (fn-scka-append-batch fn-scka-append-batch-is-body fn-scka-body
                           fn-ockp-admit-frames fn-scka-src-payloads fn-ockp-last-frame
                           fn-scka-write-step-batch fn-scka-write-step-head))))))
(local
 (defthm r6-head-buffer
 (implies (zp (nth 0 pst))
  (equal (mv-nth 3 (fn-scka-write-step pst n count s sb fb fn-arena fn-octets)) (fn-scka-head n)))
 :hints (("Goal" :in-theory (e/d (fn-scka-write-step fn-oct-append-list-is-append)
                                  (fn-scka-head fn-ockp-admit-frames fn-ockp-last-frame
                                   fn-scka-write-step-batch fn-scka-write-step-head))))))
(local
 (defthm r6-step-admission
 (let* ((r (fn-scka-write-step pst n count s sb fb fn-arena fn-octets))
        (adm (fn-ockp-admit-frames
               (fn-ockp-last-frame 0 (nfix (nth 0 pst)) count s (nth 3 pst) (mv-nth 3 r))
               (nfix (nth 4 pst)) sb fb)))
  (implies (equal (mv-nth 0 r) :ok)
           (and (equal (car adm) :ok) (equal (nth 4 (mv-nth 2 r)) (nth 1 adm)))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories '(fn-scka-write-step nth mv-nth zp nfix (:type-prescription fn-ockp-admit-frames) car-cons cdr-cons)
                            (theory 'minimal-theory))))))
(local
 (defthm r6-step-admission-width
 (let* ((r (fn-scka-write-step pst n count s sb fb fn-arena fn-octets))
        (buf (mv-nth 3 r))
        (header (fn-scc-header (nfix (nth 0 pst)) count (len buf) s)))
  (implies (and (equal (mv-nth 0 r) :ok) (true-listp buf)
                (< (len buf) *fn-scc-u64-bound*) (natp (nth 4 pst)))
           (and (equal (fn-sccr-admit-segment header (nth 4 pst) sb fb)
                        (list :ok (+ 69 (len buf)) (len buf)))
                (equal (nth 4 (mv-nth 2 r)) (+ (nth 4 pst) 69 (len buf))))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance r6-step-admission)
                (:instance r6-admit-single-header
                   (i (nfix (nth 0 pst))) (c count)
                   (l (len (mv-nth 3 (fn-scka-write-step pst n count s sb fb fn-arena fn-octets))))
                   (a 0) (b (len (mv-nth 3 (fn-scka-write-step pst n count s sb fb fn-arena fn-octets))))
                   (trailer (fn-scc-seal (nth 3 pst)
                               (fn-scc-header (nfix (nth 0 pst)) count
                                  (len (mv-nth 3 (fn-scka-write-step pst n count s sb fb fn-arena fn-octets))) s)
                               (mv-nth 3 (fn-scka-write-step pst n count s sb fb fn-arena fn-octets))))
                   (total (nfix (nth 4 pst)))))
          :in-theory (union-theories '(r6-last-frame nfix natp (:type-prescription len) nth zp car-cons cdr-cons)
                                     (theory 'minimal-theory))))))
(local
 (defthm r6-admit-frames-cons
 (implies (and (natp total) (fn-scc-octet-listp chunk) (fn-scc-octet-listp prev)
               (< (len chunk) *fn-scc-u64-bound*)
               (equal (fn-sccr-admit-segment (fn-scc-header i count (len chunk) s) total sb fb)
                      (list :ok (+ 69 (len chunk)) (len chunk))))
  (equal (fn-cth-admit-run (fn-scc-frames (cons chunk chunks) i count s prev) total sb fb)
         (fn-cth-admit-run
           (fn-scc-frames chunks (+ 1 i) count s
                          (fn-scc-seal prev (fn-scc-header i count (len chunk) s) chunk))
           (+ total 69 (len chunk)) sb fb)))
 :hints (("Goal" :do-not-induct t
          :expand ((fn-scc-frames (cons chunk chunks) i count s prev)
                   (:free (a b) (fn-cth-admit-run (cons a b) total sb fb)))
          :in-theory (union-theories '(r6-frame-admission natp nfix nth zp car-cons cdr-cons
                                      (:type-prescription len))
                                     (theory 'minimal-theory))))))
(local
 (defthm r6-len-nthcdr
 (implies (and (natp n) (<= n (len x)))
          (equal (len (nthcdr n x)) (- (len x) n)))))
(local
 (defthm r6-sum-bound
 (<= (nfix (car ks)) (fn-scka-sum ks))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-scka-sum)))))
(local
 (defthm r6-len-zero
 (equal (equal (len x) 0) (not (consp x)))))
(local
 (defthm r6-chunks-cons
 (implies (consp ks)
  (equal (fn-scka-chunks ps ks)
         (cons (fn-scka-body (take (nfix (car ks)) ps))
               (fn-scka-chunks (nthcdr (nfix (car ks)) ps) (cdr ks)))))
 :hints (("Goal" :in-theory (enable fn-scka-chunks)))))
(local
 (defthm r6-chunks-atom
 (implies (not (consp ks)) (equal (fn-scka-chunks ps ks) nil))
 :hints (("Goal" :in-theory (enable fn-scka-chunks)))))
(local
 (defthm r6-length-one-frame
 (implies (and (fn-scc-octet-listp chunk) (fn-scc-octet-listp prev))
  (equal (len (fn-scc-concat (fn-scc-frames (list chunk) i c s prev))) (+ 69 (len chunk))))
 :hints (("Goal" :in-theory (e/d (fn-scc-concat fn-scc-frames)
                                  (fn-scc-header fn-scc-seal fn-scc-octet-listp))))))
(local
 (defthm r6-arena-batch-facts
 (let* ((r (fn-scka-write-step pst n count s sb fb fn-arena fn-octets))
        (chunk (fn-scka-body (take (nfix (car (nth 2 pst)))
                                   (fn-scka-src-payloads (nth 1 pst) fn-arena)))))
  (implies (and (posp (nth 0 pst)) (natp (nth 4 pst))
                (fn-arena-p fn-arena) (fn-scka-srcs-okp (nth 1 pst) fn-arena)
                (fn-scc-octet-listp (nth 3 pst))
                (<= (nfix (car (nth 2 pst))) (len (fn-scka-src-payloads (nth 1 pst) fn-arena)))
                (< (len chunk) *fn-scc-u64-bound*) (equal (mv-nth 0 r) :ok))
   (and (equal (nth 4 (mv-nth 2 r)) (+ (nth 4 pst) 69 (len chunk)))
        (equal (len (fn-sccb-plan-octets (mv-nth 1 r) (mv-nth 3 r))) (+ 69 (len chunk)))
        (fn-scc-octet-listp (nth 3 (mv-nth 2 r)))
        (equal (fn-sccr-admit-segment (fn-scc-header (nth 0 pst) count (len chunk) s)
                                     (nth 4 pst) sb fb)
               (list :ok (+ 69 (len chunk)) (len chunk))))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-scka-write-step-batch (segment-bound sb) (file-bound fb))
                (:instance r6-step-admission-width)
                (:instance r6-body-octets (srcs (nth 1 pst)) (k (nfix (car (nth 2 pst))))))
          :in-theory (union-theories
            '(r6-batch-buffer fn-scka-body-true-listp r6-length-one-frame r6-seal-facts r6-header-shape
              fn-scka-len-src-payloads natp posp nfix (:type-prescription len))
            (theory 'minimal-theory))))))
(local
 (defthm r6-frames-atom
 (implies (not (consp chunks)) (equal (fn-scc-frames chunks i c s prev) nil))
 :hints (("Goal" :in-theory (enable fn-scc-frames)))))
(local
 (defthm r6-admit-atom
 (implies (not (consp segs)) (equal (fn-cth-admit-run segs total sb fb) (nfix total)))
 :hints (("Goal" :expand ((fn-cth-admit-run segs total sb fb))
          :in-theory (theory 'minimal-theory)))))
(local
 (defthm r6-nth-zero (equal (nth 0 x) (car x))))
(local
 (defthm r6-mv-zero (equal (mv-nth 0 x) (car x))))
(local
 (defthm r6-mv-cons
 (equal (mv-nth n (cons a b)) (if (zp n) a (mv-nth (1- n) b)))))
(local
 (defthm r6-nth-cons
 (equal (nth n (cons a b)) (if (zp n) a (nth (1- n) b)))))
(local
 (defthm r6-nat-len (natp (len x))))
(local
 (defthm r6-arena-batches-admitted
 (let ((r (fn-scka-write-run pst n count s sb fb fuel fn-arena fn-octets)))
  (implies (and (posp (nth 0 pst)) (natp (nth 4 pst))
                (equal count (+ (nth 0 pst) (len (nth 2 pst))))
                (equal (fn-scka-sum (nth 2 pst)) (len (fn-scka-src-payloads (nth 1 pst) fn-arena)))
                (fn-arena-p fn-arena) (fn-scka-srcs-okp (nth 1 pst) fn-arena)
                (fn-scc-octet-listp (nth 3 pst))
                (fn-scc-chunk-listp (fn-scka-chunks (fn-scka-src-payloads (nth 1 pst) fn-arena) (nth 2 pst)))
                (equal (mv-nth 0 r) :ok))
   (equal (fn-cth-admit-run
            (fn-scc-frames (fn-scka-chunks (fn-scka-src-payloads (nth 1 pst) fn-arena) (nth 2 pst))
                           (nth 0 pst) count s (nth 3 pst)) (nth 4 pst) sb fb)
          (+ (nth 4 pst) (len (mv-nth 1 r))))))
 :hints (("Goal" :induct (fn-scka-write-run pst n count s sb fb fuel fn-arena fn-octets)
          :expand ((:free (count) (fn-scka-write-run pst n count s sb fb fuel fn-arena fn-octets)))
          :in-theory (union-theories
           '((:induction fn-scka-write-run) fn-scka-write-donep fn-sco-at
             natp posp nfix zp r6-nth-zero r6-nth-cons r6-mv-zero r6-mv-cons car-cons cdr-cons len
             (:type-prescription len) (:type-prescription fn-scka-sum)
             fn-cwq-len-append r6-admit-atom r6-frames-atom r6-len-zero
             r6-chunks-cons r6-chunks-atom fn-scc-chunk-listp
             fn-scka-sum (:linear r6-sum-bound) r6-len-nthcdr fn-scka-src-payloads-nthcdr
             fn-scka-len-src-payloads fn-scka-srcs-okp-nthcdr
             r6-admit-frames-cons r6-body-octets)
           (theory 'minimal-theory)))
         ("Subgoal *1/4" :use ((:instance r6-sum-bound (ks (nth 2 pst))) (:instance fn-scka-write-step-batch
                                   (count (+ (car pst) (len (nth 2 pst)))) (segment-bound sb) (file-bound fb))
                               (:instance r6-arena-batch-facts (count (+ (car pst) (len (nth 2 pst))))))))))
(local
 (defthm r6-head-true (true-listp (fn-scka-head n))
 :hints (("Goal" :in-theory (enable fn-scka-head fn-scc-nat-octets)))))
(local
 (defthm r6-arena-head-facts
 (let ((r (fn-scka-write-step pst n count s sb fb fn-arena fn-octets)))
  (implies (and (zp (nth 0 pst)) (natp (nth 4 pst))
                (fn-scc-nat-encodablep n) (fn-scc-octet-listp (nth 3 pst))
                (< (len (fn-scka-head n)) *fn-scc-u64-bound*) (equal (mv-nth 0 r) :ok))
   (and (equal (nth 4 (mv-nth 2 r)) (+ (nth 4 pst) 69 (len (fn-scka-head n))))
        (equal (len (fn-sccb-plan-octets (mv-nth 1 r) (mv-nth 3 r))) (+ 69 (len (fn-scka-head n))))
        (fn-scc-octet-listp (nth 3 (mv-nth 2 r)))
        (equal (fn-sccr-admit-segment (fn-scc-header 0 count (len (fn-scka-head n)) s)
                                     (nth 4 pst) sb fb)
               (list :ok (+ 69 (len (fn-scka-head n))) (len (fn-scka-head n)))))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-scka-write-step-head (segment-bound sb) (file-bound fb))
                (:instance r6-step-admission-width))
          :in-theory (union-theories
            '(r6-head-buffer r6-head-true r6-head-octets r6-length-one-frame
              r6-seal-facts r6-header-shape natp zp nfix (:type-prescription len))
            (theory 'minimal-theory))))))
(defthm fn-cth-arena-write-is-admitted
(let* ((ps (fn-scka-src-payloads srcs fn-arena))
         (r (fn-scka-write-run (fn-scka-initial-state srcs ks t0) (len ps) (+ 1 (len ks))
                               s segment-bound file-bound fuel fn-arena fn-octets)))
    (implies (and (natp t0)
                  (fn-arena-p fn-arena)
                  (fn-scka-srcs-okp srcs fn-arena)
                  (fn-scc-nat-encodablep (len ps))
                  (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                  (equal (fn-scka-sum ks) (len ps))
                  (equal (mv-nth 0 r) :ok))
             (equal (fn-cth-admit-run (fn-scka-run-segments ps ks s) t0 segment-bound file-bound)
                    (+ t0 (len (mv-nth 1 r))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-scka-write-step-head (pst (fn-scka-initial-state srcs ks t0)) (n (len (fn-scka-src-payloads srcs fn-arena))) (count (+ 1 (len ks))))
       (:instance r6-arena-head-facts (pst (fn-scka-initial-state srcs ks t0)) (n (len (fn-scka-src-payloads srcs fn-arena))) (count (+ 1 (len ks))) (sb segment-bound) (fb file-bound))
       (:instance r6-arena-batches-admitted (pst (mv-nth 2 (fn-scka-write-step (fn-scka-initial-state srcs ks t0) (len (fn-scka-src-payloads srcs fn-arena)) (+ 1 (len ks)) s segment-bound file-bound fn-arena fn-octets)))
          (n (len (fn-scka-src-payloads srcs fn-arena))) (count (+ 1 (len ks))) (sb segment-bound) (fb file-bound)
          (fuel (1- fuel)) (fn-octets (mv-nth 3 (fn-scka-write-step (fn-scka-initial-state srcs ks t0) (len (fn-scka-src-payloads srcs fn-arena)) (+ 1 (len ks)) s segment-bound file-bound fn-arena fn-octets)))))
 :expand ((:free (pst n count)
            (fn-scka-write-run pst n count s segment-bound file-bound fuel fn-arena fn-octets)))
 :in-theory (union-theories
  '(fn-scka-initial-state fn-scka-write-donep fn-sco-at fn-scka-run-segments fn-scka-run-chunks
    fn-scc-chunk-listp r6-admit-frames-cons r6-head-octets
    r6-nth-zero r6-nth-cons r6-mv-zero r6-mv-cons car-cons cdr-cons
    natp posp nfix zp len (:type-prescription len)
    fn-cwq-len-append fn-scka-len-src-payloads
    (:executable-counterpart fn-scc-octet-listp))
  (theory 'minimal-theory)))))
)

; K8t (proof: Codex round 6, review-ct2/r6-k8t.lsp, helpers local).
(encapsulate ()
(local
 (include-book "arithmetic/top" :dir :system))
(local
 (in-theory (disable fn-sccr-cbor-octet-listp-is-scc-octet-listp
                    fn-sccr-scc-octet-listp-is-cbor-octet-listp
                    fn-oct-bufp-true-listp fn-octets$c-bufp)))
(local
 (defthm r6-u64-true (true-listp (fn-scc-u64 n k))))
(local
 (defthm r6-header-shape
 (and (true-listp (fn-scc-header i c l s))
      (equal (len (fn-scc-header i c l s)) 37)
      (fn-scc-octet-listp (fn-scc-header i c l s)))
 :hints (("Goal" :in-theory (e/d (fn-scc-header fn-scc-octetp) (fn-scc-u64))))))
(local
 (defthm r6-take-append
 (implies (and (true-listp a) (natp k) (<= k (len a)))
          (equal (take k (append a b)) (take k a)))))
(local
 (defthm r6-drop-append
 (implies (equal k (len a)) (equal (nthcdr k (append a b)) b))))
(local
 (defthm r6-long-len
 (implies (natp k) (equal (fn-scc-long-enoughp k a) (<= k (len a))))))
(local
 (defthm r6-octets-append
 (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
          (fn-scc-octet-listp (append a b)))
 :hints (("Goal" :induct (fn-scc-octet-listp a)
                 :in-theory (e/d (fn-scc-octet-listp) (fn-scc-octet-listp-facts))))))
(local
 (defthm r6-take-all
 (implies (and (true-listp x) (equal k (len x))) (equal (take k x) x))))
(local
 (defthm r6-u64-value
 (implies (and (natp n) (natp k) (< n (expt 256 k)))
          (equal (fn-scc-le-value (fn-scc-u64 n k)) n))
 :hints (("Goal" :induct (fn-scc-u64 n k)))))
(local
 (defthm r6-u64-read
 (implies (and (natp n) (< n *fn-scc-u64-bound*))
          (equal (fn-scc-u64-at (append (fn-scc-u64 n 8) rest)) n))
 :hints (("Goal" :in-theory (e/d (fn-scc-u64-at) (fn-scc-u64))))))
(local
 (defthm r6-header-admit
 (implies (and (natp l) (< l *fn-scc-u64-bound*))
  (equal (fn-sccr-admit-segment (fn-scc-header i c l s) total sb fb)
         (if (and (natp total) (natp sb) (natp fb)
                  (<= (+ 69 l) sb) (<= (+ total 69 l) fb))
             (list :ok (+ 69 l) l) (list :refused :exceeds-bound))))
 :hints (("Goal" :do-not-induct t :use ((:instance r6-header-shape))
          :in-theory (e/d (fn-sccr-admit-segment fn-scc-header fn-scc-parse-header fn-scc-u64-at)
                          (fn-scc-u64 fn-scc-le-value r6-header-shape))))))
(local
 (defthm r6-seal-facts
 (implies (and (fn-scc-octet-listp prev) (fn-scc-octet-listp header) (fn-scc-octet-listp chunk))
  (and (fn-scc-octet-listp (fn-scc-seal prev header chunk))
       (true-listp (fn-scc-seal prev header chunk))
       (equal (len (fn-scc-seal prev header chunk)) 32)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-frame-trailer-is-a-digest (octets (append prev header chunk))))
          :in-theory (e/d (fn-scc-seal fn-frame-digestp)
                          (fn-frame-trailer-is-a-digest))))))
(local
 (defthm r6-nth-append
 (implies (and (natp n) (< n (len a)))
          (equal (nth n (append a b)) (nth n a)))))
(local
 (defthm r6-admit-header-append
 (implies (and (fn-scc-octet-listp header) (equal (len header) 37)
               (fn-scc-octet-listp rest))
  (equal (fn-sccr-admit-segment (append header rest) total sb fb)
         (fn-sccr-admit-segment header total sb fb)))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-sccr-admit-segment fn-sccr-parse-header-of-append fn-sccr-other-schemap)
                          (fn-scc-parse-header fn-scc-octet-listp))))))
(local
 (defthm r6-frame-admission
 (implies (and (fn-scc-octet-listp chunk) (fn-scc-octet-listp prev)
               (< (len chunk) *fn-scc-u64-bound*))
  (equal (fn-sccr-admit-segment
           (append (fn-scc-header i c (len chunk) s) chunk
                   (fn-scc-seal prev (fn-scc-header i c (len chunk) s) chunk)) total sb fb)
         (fn-sccr-admit-segment (fn-scc-header i c (len chunk) s) total sb fb)))
 :hints (("Goal" :in-theory (union-theories
           '(r6-admit-header-append r6-header-shape r6-octets-append r6-seal-facts)
           (theory 'minimal-theory))))))
(local
 (defthm r6-frame-length
 (implies (and (fn-scc-octet-listp chunk) (fn-scc-octet-listp prev))
  (equal (len (append (fn-scc-header i c (len chunk) s) chunk
                     (fn-scc-seal prev (fn-scc-header i c (len chunk) s) chunk)))
         (+ 69 (len chunk))))
 :hints (("Goal" :in-theory (e/d () (fn-scc-header fn-scc-seal fn-scc-octet-listp))))))
(local
 (defthm r6-admit-frames-cons
 (implies (and (natp total) (fn-scc-octet-listp chunk) (fn-scc-octet-listp prev)
               (< (len chunk) *fn-scc-u64-bound*)
               (equal (fn-sccr-admit-segment (fn-scc-header i count (len chunk) s) total sb fb)
                      (list :ok (+ 69 (len chunk)) (len chunk))))
  (equal (fn-cth-admit-run (fn-scc-frames (cons chunk chunks) i count s prev) total sb fb)
         (fn-cth-admit-run
           (fn-scc-frames chunks (+ 1 i) count s
                          (fn-scc-seal prev (fn-scc-header i count (len chunk) s) chunk))
           (+ total 69 (len chunk)) sb fb)))
 :hints (("Goal" :do-not-induct t
          :expand ((fn-scc-frames (cons chunk chunks) i count s prev)
                   (:free (a b) (fn-cth-admit-run (cons a b) total sb fb)))
          :in-theory (union-theories '(r6-frame-admission natp nfix nth zp car-cons cdr-cons
                                      (:type-prescription len))
                                     (theory 'minimal-theory))))))
(local
 (defthm r6-len-nthcdr
 (implies (and (natp n) (<= n (len x)))
          (equal (len (nthcdr n x)) (- (len x) n)))))
(local
 (defthm r6-sum-bound
 (<= (nfix (car ks)) (fn-scka-sum ks))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-scka-sum)))))
(local
 (defthm r6-len-zero
 (equal (equal (len x) 0) (not (consp x)))))
(local
 (defthm r6-chunks-cons
 (implies (consp ks)
  (equal (fn-scka-chunks ps ks)
         (cons (fn-scka-body (take (nfix (car ks)) ps))
               (fn-scka-chunks (nthcdr (nfix (car ks)) ps) (cdr ks)))))
 :hints (("Goal" :in-theory (enable fn-scka-chunks)))))
(local
 (defthm r6-chunks-atom
 (implies (not (consp ks)) (equal (fn-scka-chunks ps ks) nil))
 :hints (("Goal" :in-theory (enable fn-scka-chunks)))))
(local
 (defthm r6-nth-zero (equal (nth 0 x) (car x))))
(local
 (defthm r6-mv-zero (equal (mv-nth 0 x) (car x))))
(local
 (defthm r6-mv-cons
 (equal (mv-nth n (cons a b)) (if (zp n) a (mv-nth (1- n) b)))))
(local
 (defthm r6-nth-cons
 (equal (nth n (cons a b)) (if (zp n) a (nth (1- n) b)))))
(local
 (defthm r6-nat-len (natp (len x))))
(local
 (defthm r6-frames-atom
 (implies (not (consp chunks)) (equal (fn-scc-frames chunks i c s prev) nil))
 :hints (("Goal" :in-theory (enable fn-scc-frames)))))
(local
 (defthm r6-admit-atom
 (implies (not (consp segs)) (equal (fn-cth-admit-run segs total sb fb) (nfix total)))
 :hints (("Goal" :expand ((fn-cth-admit-run segs total sb fb))
          :in-theory (theory 'minimal-theory)))))
(local
 (defun r6t-scan (bytes total sb fb)
 (declare (xargs :measure (len bytes) :verify-guards nil))
 (if (not (consp bytes)) (nfix total)
   (let* ((a (fn-sccr-admit-segment (take 37 bytes) total sb fb)) (extent (nth 1 a)))
    (if (and (eq (car a) :ok) (posp extent) (<= extent (len bytes)))
        (r6t-scan (nthcdr extent bytes) (+ (nfix total) extent) sb fb)
      :refused)))))
(local
 (defthm r6t-consp-append (equal (consp (append a b)) (or (consp a) (consp b)))))
(local
 (defthm r6t-len-true-fix (equal (len (true-list-fix x)) (len x))))
(local
 (defthm r6t-len-take (equal (len (take n x)) (nfix n))))
(local
 (defthm r6t-append-assoc (equal (append (append a b) c) (append a (append b c)))))
(local
 (defthm r6t-append-nil (implies (true-listp x) (equal (append x nil) x))))
(local
 (defthm r6t-true-fix (implies (true-listp x) (equal (true-list-fix x) x))))
(local
 (defthm r6t-scan-prefix
 (implies (and (true-listp prefix) (natp total)
               (equal (fn-sccr-admit-segment (take 37 prefix) total sb fb)
                      (list :ok (len prefix) chunk))
               (<= 37 (len prefix)))
  (equal (r6t-scan (append prefix rest) total sb fb)
         (r6t-scan rest (+ total (len prefix)) sb fb)))
 :hints (("Goal" :do-not-induct t
          :expand ((r6t-scan (append prefix rest) total sb fb))
          :in-theory (e/d (posp) (r6t-scan fn-sccr-admit-segment take nthcdr))))))
(local
 (defthm r6t-scan-nil
 (equal (r6t-scan nil total sb fb) (nfix total))
 :hints (("Goal" :expand ((r6t-scan nil total sb fb))))))
(local
 (defthm r6t-header-parse
 (implies (and (natp l) (< l *fn-scc-u64-bound*))
  (and (fn-scc-parse-header (fn-scc-header i c l s))
       (equal (nth 2 (fn-scc-parse-header (fn-scc-header i c l s))) l)))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-scc-header fn-scc-parse-header fn-scc-u64-at)
                 (fn-scc-u64 fn-scc-le-value))))))
(local
 (defun r6t-framep (f buf)
 (declare (xargs :guard t :verify-guards nil))
 (let ((h (nth 0 f)) (a (nth 1 f)) (b (nth 2 f)) (tr (nth 3 f)))
  (and (fn-scc-octet-listp h) (equal (len h) 37) (fn-scc-parse-header h)
       (natp a) (natp b) (<= a b) (<= b (len buf))
       (equal (nth 2 (fn-scc-parse-header h)) (- b a))
       (true-listp tr) (equal (len tr) 32)))))
(local
 (defun r6t-planp (frames buf)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp frames) (and (r6t-framep (car frames) buf) (r6t-planp (cdr frames) buf)) t)))
(local
 (defthm r6t-frame-facts
 (implies (and (true-listp buf) (r6t-framep f buf))
  (and (true-listp (fn-sccb-frame-octets f buf))
       (equal (take 37 (fn-sccb-frame-octets f buf)) (nth 0 f))
       (equal (len (fn-sccb-frame-octets f buf)) (+ 69 (- (nth 2 f) (nth 1 f))))))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (r6t-framep fn-sccb-frame-octets fn-sccb-slice-acc-is-slice-list
                  fn-oct-slice-list-is-take-nthcdr)
                 (fn-scc-parse-header fn-scc-octet-listp fn-oct-slice-list take nthcdr))))))
(local
 (defthm r6t-frame-admit-extent
 (implies (and (r6t-framep f buf)
               (equal (car (fn-sccr-admit-segment (nth 0 f) total sb fb)) :ok))
  (equal (fn-sccr-admit-segment (nth 0 f) total sb fb)
         (list :ok (+ 69 (- (nth 2 f) (nth 1 f))) (- (nth 2 f) (nth 1 f)))))
 :hints (("Goal" :in-theory (e/d (r6t-framep fn-sccr-admit-segment)
                                  (fn-scc-parse-header fn-scc-octet-listp))))))
(local
 (defthm r6t-frame-scan
 (implies (and (true-listp buf) (r6t-framep f buf) (natp total)
               (equal (car (fn-sccr-admit-segment (nth 0 f) total sb fb)) :ok))
  (equal (r6t-scan (append (fn-sccb-frame-octets f buf) rest) total sb fb)
         (r6t-scan rest (+ total (len (fn-sccb-frame-octets f buf))) sb fb)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance r6t-frame-admit-extent) (:instance r6t-frame-facts)
       (:instance r6t-scan-prefix (prefix (fn-sccb-frame-octets f buf))
                  (chunk (- (nth 2 f) (nth 1 f)))))
 :in-theory (e/d (r6t-framep) (r6t-scan fn-sccb-frame-octets fn-sccr-admit-segment
                            fn-scc-octet-listp fn-scc-parse-header r6t-scan-prefix))))))
(local
 (defthm r6t-plan-scan
 (implies (and (true-listp buf) (r6t-planp frames buf) (natp total)
               (equal (car (fn-ockp-admit-frames frames total sb fb)) :ok))
  (and (equal (nth 1 (fn-ockp-admit-frames frames total sb fb))
              (+ total (len (fn-sccb-plan-octets frames buf))))
       (equal (r6t-scan (append (fn-sccb-plan-octets frames buf) rest) total sb fb)
              (r6t-scan rest (nth 1 (fn-ockp-admit-frames frames total sb fb)) sb fb))))
 :hints (("Goal" :induct (fn-ockp-admit-frames frames total sb fb)
 :in-theory (union-theories
  '(associativity-of-+ commutativity-of-+ commutativity-2-of-+ fn-ockp-admit-frames fn-sccb-plan-octets r6t-planp r6t-frame-facts r6t-frame-admit-extent
    r6t-frame-scan r6t-append-assoc fn-cwq-len-append binary-append
    natp nfix r6-nth-cons zp car-cons cdr-cons len (:type-prescription len))
  (theory 'minimal-theory))))))
(local
 (defthm r6t-octets-nthcdr
 (implies (fn-scc-octet-listp x) (fn-scc-octet-listp (nthcdr n x)))
 :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))))
(local
 (defthm r6t-octets-take
 (implies (and (fn-scc-octet-listp x) (natp n) (<= n (len x)))
          (fn-scc-octet-listp (take n x)))
 :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))))
(local
 (defthm r6t-slice-octets
 (implies (and (fn-scc-octet-listp buf) (natp a) (natp b) (<= a b) (<= b (len buf)))
          (fn-scc-octet-listp (fn-sccb-slice-acc a b nil buf)))
 :hints (("Goal" :in-theory (e/d (fn-sccb-slice-acc-is-slice-list fn-oct-slice-list-is-take-nthcdr)
                                  (fn-scc-octet-listp fn-oct-slice-list))))))
(local
 (defthm r6t-plan-append
 (equal (r6t-planp (append x y) buf) (and (r6t-planp x buf) (r6t-planp y buf)))
 :hints (("Goal" :in-theory (disable r6t-framep)))))
(local
 (defthm r6t-plan-revappend
 (equal (r6t-planp (revappend x y) buf) (and (r6t-planp x buf) (r6t-planp y buf)))
 :hints (("Goal" :in-theory (disable r6t-framep)))))
(local
 (defthm r6t-cut-good
 (implies (and (natp a) (<= a (len fn-octets)) (natp index) (natp seg)
               (fn-scc-octet-listp fn-octets) (fn-scc-octet-listp prev)
               (< (len fn-octets) *fn-scc-u64-bound*) (r6t-planp acc fn-octets))
  (let ((r (fn-ockp-cut-frames a index count s prev seg acc fn-octets)))
   (and (r6t-planp (mv-nth 0 r) fn-octets)
        (natp (mv-nth 1 r)) (<= a (mv-nth 1 r)) (<= (mv-nth 1 r) (len fn-octets))
        (fn-scc-octet-listp (mv-nth 2 r)) (natp (mv-nth 3 r)))))
 :hints (("Goal" :induct (fn-ockp-cut-frames a index count s prev seg acc fn-octets)
          :in-theory (e/d (fn-ockp-cut-frames r6t-planp r6t-framep)
                          (fn-scc-header fn-scc-seal fn-scc-octet-listp fn-scc-parse-header
                           fn-sccb-slice-acc fn-sccr-admit-segment))))))
(local
 (defthm r6t-last-good
 (implies (and (natp a) (<= a (len fn-octets))
               (fn-scc-octet-listp fn-octets) (fn-scc-octet-listp prev)
               (< (len fn-octets) *fn-scc-u64-bound*))
          (r6t-planp (fn-ockp-last-frame a index count s prev fn-octets) fn-octets))
 :hints (("Goal" :in-theory (e/d (fn-ockp-last-frame r6t-planp r6t-framep)
                                  (fn-scc-header fn-scc-seal fn-scc-octet-listp fn-scc-parse-header
                                   fn-sccb-slice-acc fn-sccr-admit-segment))))))
(local
 (defun r6t-take-ind (b rows i)
 (if (or (zp b) (not (consp rows))) (list rows i)
   (r6t-take-ind (1- b) (cdr rows) (+ 1 i)))))
(local
 (defthm r6t-rows-split
 (implies (natp i)
  (equal (fn-sct-rows-program rows i selfp mtrie n table)
         (append (fn-sct-rows-program (fn-ockp-take b rows) i selfp mtrie n table)
                 (fn-sct-rows-program (fn-ockp-drop b rows) (+ i (len (fn-ockp-take b rows)))
                                      selfp mtrie n table))))
 :rule-classes nil
 :hints (("Goal" :induct (r6t-take-ind b rows i)
 :in-theory (e/d (fn-sct-rows-program) (fn-sct-program))))))
(local
 (defthm r6t-residue
 (implies (and (natp w) (<= w (len buf)) (true-listp buf))
  (equal (fn-sccb-slice-acc w (len buf) nil buf) (nthcdr w buf)))
 :hints (("Goal" :in-theory (enable fn-sccb-slice-acc-is-slice-list)))))
(local
 (defthm r6t-encode-splits-payload
 (let ((r (fn-ockp-encode-batch rest i b bytes selfp mtrie n table fn-octets)))
  (implies (and (true-listp fn-octets) (natp i) (mv-nth 0 r))
   (and (natp (mv-nth 2 r)) (true-listp (mv-nth 3 r))
        (equal (append (mv-nth 3 r) (fn-sct-rows-program (mv-nth 1 r) (mv-nth 2 r) selfp mtrie n table))
               (append fn-octets (fn-sct-rows-program rest i selfp mtrie n table))))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-ockp-encode-batch-ok-is-encodable)
       (:instance fn-ockp-encode-batch-is-rows-program)
       (:instance r6t-rows-split (rows rest)
                  (b (fn-ockp-batch-rows rest i b bytes selfp mtrie n table (len fn-octets)))))
 :in-theory (e/d () (fn-ockp-encode-batch fn-sct-rows-program fn-sct-program fn-ockp-batch-rows
                     fn-ockp-take fn-ockp-drop fn-ockp-rows-encodablep))))))
(local
 (defun r6t-payloadp (p)
 (and (fn-scc-octet-listp p) (< (len p) *fn-scc-u64-bound*))))
(local
 (defthm r6t-octets-append-parts
 (implies (true-listp x)
  (equal (fn-scc-octet-listp (append x y))
         (and (fn-scc-octet-listp x) (fn-scc-octet-listp y))))
 :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))))
(local
 (defthm r6t-payload-prefix
 (implies (and (true-listp x) (r6t-payloadp (append x y))) (r6t-payloadp x))
 :hints (("Goal" :in-theory (enable r6t-payloadp)))))
(local
 (defthm r6t-payload-drop
 (implies (and (natp a) (<= a (len x)) (true-listp x) (r6t-payloadp (append x y)))
  (r6t-payloadp (append (nthcdr a x) y)))
 :hints (("Goal" :in-theory (e/d (r6t-payloadp) (fn-scc-octet-listp))))))
(local
 (defun r6t-later-good (tables k n mtrie table)
 (declare (xargs :measure (nfix (- 4 (nfix k))) :verify-guards nil))
 (if (or (not (natp k)) (>= k 4)) t
  (and (r6t-payloadp (fn-sct-rows-program (fn-ockp-table-rows tables k) 0 (equal k 2)
                                         (if (equal k 3) mtrie nil) n table))
       (r6t-later-good tables (+ 1 k) n mtrie table)))))
(local
 (defthm r6t-encode-good
 (let ((r (fn-ockp-encode-batch rest i b bytes selfp mtrie n table fn-octets)))
  (implies (and (true-listp fn-octets) (natp i) (mv-nth 0 r)
                (r6t-payloadp (append fn-octets (fn-sct-rows-program rest i selfp mtrie n table))))
   (and (natp (mv-nth 2 r)) (true-listp (mv-nth 3 r)) (r6t-payloadp (mv-nth 3 r))
        (r6t-payloadp (append (mv-nth 3 r)
                              (fn-sct-rows-program (mv-nth 1 r) (mv-nth 2 r) selfp mtrie n table))))))
 :hints (("Goal" :do-not-induct t :use ((:instance r6t-encode-splits-payload)
         (:instance r6t-payload-prefix
           (x (mv-nth 3 (fn-ockp-encode-batch rest i b bytes selfp mtrie n table fn-octets)))
           (y (fn-sct-rows-program
                (mv-nth 1 (fn-ockp-encode-batch rest i b bytes selfp mtrie n table fn-octets))
                (mv-nth 2 (fn-ockp-encode-batch rest i b bytes selfp mtrie n table fn-octets))
                selfp mtrie n table))))
 :in-theory (e/d () (r6t-encode-splits-payload fn-ockp-encode-batch fn-sct-rows-program
                     r6t-payloadp fn-ockp-rows-encodablep fn-ockp-encode-batch-is-rows-program))))))
(local
 (defun r6t-invp (tables k rest i index prev w total n mtrie table buf)
 (declare (xargs :guard t :verify-guards nil))
 (and (natp k) (natp i) (natp index) (natp w) (natp total)
      (true-listp buf) (<= w (len buf)) (fn-scc-octet-listp prev)
      (or (>= k 4)
          (and (r6t-payloadp (append (nthcdr w buf)
                                     (fn-sct-rows-program rest i (equal k 2)
                                                          (if (equal k 3) mtrie nil) n table)))
               (r6t-later-good tables (+ 1 k) n mtrie table))))))
(local
 (defthm r6t-admit-total-natp
 (implies (and (natp total) (equal (car (fn-ockp-admit-frames frames total sb fb)) :ok))
          (natp (nth 1 (fn-ockp-admit-frames frames total sb fb))))
 :hints (("Goal" :induct (fn-ockp-admit-frames frames total sb fb)
 :in-theory (union-theories '(fn-ockp-admit-frames natp nfix r6-nth-cons car-cons cdr-cons zp)
                            (theory 'minimal-theory))))))
(local
 (defthm r6t-nthcdr-at-fill
 (implies (and (true-listp buf) (natp w) (<= (len buf) w)) (equal (nthcdr w buf) nil))))
(local
 (defthm r6t-later-good-unfold
 (implies (and (natp k) (< k 4))
  (equal (r6t-later-good tables k n mtrie table)
         (and (r6t-payloadp (fn-sct-rows-program (fn-ockp-table-rows tables k) 0 (equal k 2)
                                                (if (equal k 3) mtrie nil) n table))
              (r6t-later-good tables (+ 1 k) n mtrie table))))
 :hints (("Goal" :expand ((r6t-later-good tables k n mtrie table))))))
(local
 (defthm r6t-plan-atom (implies (not (consp frames)) (r6t-planp frames buf))))
(local
 (defthm r6t-later-done
 (implies (or (not (natp k)) (>= k 4)) (r6t-later-good tables k n mtrie table))))
(local
 (defthm r6t-batch-facts
 (let ((r (fn-ockp-batch tables k rest i index prev w b bytes seg s counts n mtrie table total sb fb fn-octets)))
  (implies (and (r6t-invp tables k rest i index prev w total n mtrie table fn-octets)
                (< k 4) (natp seg) (equal (mv-nth 0 r) :ok))
   (and (r6t-invp tables (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r)
                 (mv-nth 6 r) (mv-nth 7 r) (mv-nth 8 r) n mtrie table (mv-nth 9 r))
        (r6t-planp (mv-nth 1 r) (mv-nth 9 r))
        (equal (car (fn-ockp-admit-frames (mv-nth 1 r) total sb fb)) :ok)
        (equal (mv-nth 8 r) (nth 1 (fn-ockp-admit-frames (mv-nth 1 r) total sb fb))))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance r6t-encode-good (fn-octets (nthcdr w fn-octets))
                  (selfp (equal k 2)) (mtrie (if (equal k 3) mtrie nil)))
       (:instance r6t-cut-good (a 0) (acc nil) (count (fn-ockp-count counts k)) (fn-octets (mv-nth 3 (fn-ockp-encode-batch rest i b bytes (equal k 2) (if (equal k 3) mtrie nil) n table (nthcdr w fn-octets)))))
       (:instance r6t-last-good (a (mv-nth 1 (fn-ockp-cut-frames 0 index (fn-ockp-count counts k) s prev seg nil (mv-nth 3 (fn-ockp-encode-batch rest i b bytes (equal k 2) (if (equal k 3) mtrie nil) n table (nthcdr w fn-octets)))))) (index (mv-nth 3 (fn-ockp-cut-frames 0 index (fn-ockp-count counts k) s prev seg nil (mv-nth 3 (fn-ockp-encode-batch rest i b bytes (equal k 2) (if (equal k 3) mtrie nil) n table (nthcdr w fn-octets)))))) (prev (mv-nth 2 (fn-ockp-cut-frames 0 index (fn-ockp-count counts k) s prev seg nil (mv-nth 3 (fn-ockp-encode-batch rest i b bytes (equal k 2) (if (equal k 3) mtrie nil) n table (nthcdr w fn-octets))))))
                  (count (fn-ockp-count counts k)) (fn-octets (mv-nth 3 (fn-ockp-encode-batch rest i b bytes (equal k 2) (if (equal k 3) mtrie nil) n table (nthcdr w fn-octets)))))
       (:instance r6t-payload-drop (a (mv-nth 1 (fn-ockp-cut-frames 0 index (fn-ockp-count counts k) s prev seg nil (mv-nth 3 (fn-ockp-encode-batch rest i b bytes (equal k 2) (if (equal k 3) mtrie nil) n table (nthcdr w fn-octets)))))) (x (mv-nth 3 (fn-ockp-encode-batch rest i b bytes (equal k 2) (if (equal k 3) mtrie nil) n table (nthcdr w fn-octets))))
                  (y (fn-sct-rows-program (mv-nth 1 (fn-ockp-encode-batch rest i b bytes (equal k 2) (if (equal k 3) mtrie nil) n table (nthcdr w fn-octets))) (mv-nth 2 (fn-ockp-encode-batch rest i b bytes (equal k 2) (if (equal k 3) mtrie nil) n table (nthcdr w fn-octets))) (equal k 2) (if (equal k 3) mtrie nil) n table))))
 :in-theory (e/d (fn-ockp-batch r6t-invp r6t-payloadp fn-oct-append-list-is-append)
                 (nth mv-nth nthcdr r6t-plan-scan fn-sccb-plan-octets fn-ockp-rows-program-octets fn-ockp-program-octets
                  fn-ockp-encode-batch fn-ockp-encode-batch-is-rows-program fn-ockp-cut-frames fn-ockp-last-frame
                  fn-ockp-admit-frames fn-ockp-table-rows fn-ockp-count fn-sct-rows-program fn-sct-program
                  fn-scc-octet-listp fn-scc-header fn-scc-seal r6t-planp r6t-framep r6t-later-good
                  fn-sccb-slice-acc fn-sccb-slice-acc-is-slice-list fn-sccr-admit-segment
                  r6t-encode-good r6t-cut-good r6t-last-good r6t-payload-drop))))))
(local
 (defun r6t-loop-invp (setup pst buf)
 (r6t-invp (nth 1 setup) (nth 0 pst) (nth 1 pst) (nth 2 pst) (nth 3 pst)
           (nth 4 pst) (nth 5 pst) (nth 6 pst) (nfix (nth 5 setup)) (nth 3 setup) (nth 4 setup) buf)))
(local
 (defthm r6t-loop-facts
 (implies (r6t-loop-invp setup pst buf)
  (and (natp (nth 0 pst)) (natp (nth 2 pst)) (natp (nth 3 pst)) (natp (nth 5 pst))
       (natp (nth 6 pst)) (true-listp buf) (<= (nth 5 pst) (len buf))))
 :hints (("Goal" :in-theory (union-theories '(r6t-loop-invp r6t-invp) (theory 'minimal-theory))))))
(local
 (defthm r6t-step-facts
 (let ((r (fn-ockp-step setup pst b bytes seg s sb fb fn-octets)))
  (implies (and (r6t-loop-invp setup pst fn-octets) (< (nth 0 pst) 4) (natp seg)
                (equal (mv-nth 0 r) :ok))
   (and (r6t-loop-invp setup (mv-nth 2 r) (mv-nth 3 r))
        (r6t-planp (mv-nth 1 r) (mv-nth 3 r))
        (equal (car (fn-ockp-admit-frames (mv-nth 1 r) (nth 6 pst) sb fb)) :ok)
        (equal (nth 6 (mv-nth 2 r))
               (nth 1 (fn-ockp-admit-frames (mv-nth 1 r) (nth 6 pst) sb fb))))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance r6t-batch-facts (tables (nth 1 setup)) (k (nth 0 pst)) (rest (nth 1 pst))
        (i (nth 2 pst)) (index (nth 3 pst)) (prev (nth 4 pst)) (w (nth 5 pst))
        (total (nth 6 pst)) (counts (nth 2 setup)) (n (nfix (nth 5 setup)))
        (mtrie (nth 3 setup)) (table (nth 4 setup))))
 :in-theory (union-theories '(fn-ockp-step fn-sco-at r6t-loop-invp r6-nth-cons r6-mv-cons r6-mv-zero
                              car-cons cdr-cons zp) (theory 'minimal-theory))))))
(local
 (defthm r6t-loop-types
 (implies (r6t-loop-invp setup pst buf)
  (and (integerp (nth 0 pst)) (<= 0 (nth 0 pst))
       (integerp (nth 6 pst)) (<= 0 (nth 6 pst))
       (true-listp buf)))
 :rule-classes ((:forward-chaining :trigger-terms ((r6t-loop-invp setup pst buf))))
 :hints (("Goal" :use r6t-loop-facts :in-theory (union-theories '(natp) (theory 'minimal-theory))))))
(local
 (defthm r6t-step-scan
 (let* ((r (fn-ockp-step setup pst b bytes seg s sb fb fn-octets))
        (out (fn-sccb-plan-octets (mv-nth 1 r) (mv-nth 3 r))))
  (implies (and (r6t-loop-invp setup pst fn-octets) (< (nth 0 pst) 4) (natp seg)
                (equal (mv-nth 0 r) :ok))
   (and (equal (nth 6 (mv-nth 2 r)) (+ (nth 6 pst) (len out)))
        (equal (r6t-scan (append out more) (nth 6 pst) sb fb)
               (r6t-scan more (+ (nth 6 pst) (len out)) sb fb)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance r6t-step-facts)
       (:instance r6t-loop-facts (buf fn-octets))
       (:instance r6t-loop-facts (pst (mv-nth 2 (fn-ockp-step setup pst b bytes seg s sb fb fn-octets)))
          (buf (mv-nth 3 (fn-ockp-step setup pst b bytes seg s sb fb fn-octets))))
       (:instance r6t-plan-scan (frames (mv-nth 1 (fn-ockp-step setup pst b bytes seg s sb fb fn-octets)))
          (buf (mv-nth 3 (fn-ockp-step setup pst b bytes seg s sb fb fn-octets)))
          (total (nth 6 pst)) (rest more)))
 :in-theory (union-theories '(natp r6-mv-zero) (set-difference-theories (theory 'minimal-theory) '(nth mv-nth)))))))
(local
 (defthm r6t-run-scan
 (let ((r (fn-ockp-run setup pst b bytes seg s sb fb fuel fn-octets)))
  (implies (and (r6t-loop-invp setup pst fn-octets) (natp seg) (equal (mv-nth 0 r) :ok))
   (equal (r6t-scan (mv-nth 1 r) (nth 6 pst) sb fb) (+ (nth 6 pst) (len (mv-nth 1 r))))))
 :hints (("Goal" :do-not '(eliminate-destructors generalize) :induct (fn-ockp-run setup pst b bytes seg s sb fb fuel fn-octets)
 :expand ((fn-ockp-run setup pst b bytes seg s sb fb fuel fn-octets))
 :in-theory (union-theories
  '((:induction fn-ockp-run) fn-ockp-donep fn-sco-at r6t-loop-facts r6t-loop-types r6t-step-facts r6t-step-scan
    r6t-scan-nil natp nfix zp r6-mv-cons r6-mv-zero r6-nth-cons car-cons cdr-cons
    fn-cwq-len-append len (:type-prescription len) associativity-of-+ commutativity-of-+ commutativity-2-of-+)
  (set-difference-theories (theory 'minimal-theory) '(mv-nth nth)))) 
)))
(local
 (defthm r6t-take-drop
 (implies (and (true-listp x) (natp n) (<= n (len x)))
          (equal (append (take n x) (nthcdr n x)) x))))
(local
 (defthm r6t-admit-take37
 (implies (and (fn-scc-octet-listp x) (<= 37 (len x)))
  (equal (fn-sccr-admit-segment (take 37 x) total sb fb)
         (fn-sccr-admit-segment x total sb fb)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance r6-admit-header-append (header (take 37 x)) (rest (nthcdr 37 x))))
 :in-theory (e/d () (r6-admit-header-append fn-sccr-admit-segment fn-scc-octet-listp take nthcdr))))))
(local
 (defun r6t-segmentp (x)
 (and (fn-scc-octet-listp x) (<= 37 (len x)) (fn-scc-parse-header x)
      (equal (len x) (+ 69 (nth 2 (fn-scc-parse-header x)))))))
(local
 (defun r6t-segmentsp (xs)
 (if (consp xs) (and (r6t-segmentp (car xs)) (r6t-segmentsp (cdr xs))) t)))
(local
 (defthm r6t-segment-admit
 (implies (r6t-segmentp x)
  (equal (fn-sccr-admit-segment x total sb fb)
   (if (and (natp total) (natp sb) (natp fb) (<= (len x) sb) (<= (+ total (len x)) fb))
       (list :ok (len x) (- (len x) 69)) (list :refused :exceeds-bound))))
 :hints (("Goal" :in-theory (e/d (r6t-segmentp fn-sccr-admit-segment)
                                  (fn-scc-octet-listp fn-scc-parse-header))))))
(local
 (defthm r6t-segment-scan
 (implies (and (r6t-segmentp x) (natp total))
  (equal (r6t-scan (append x rest) total sb fb)
   (if (equal (car (fn-sccr-admit-segment x total sb fb)) :ok)
       (r6t-scan rest (+ total (len x)) sb fb) :refused)))
 :hints (("Goal" :do-not-induct t :expand ((r6t-scan (append x rest) total sb fb))
 :in-theory (e/d (r6t-segmentp posp)
                 (r6t-scan fn-sccr-admit-segment fn-scc-parse-header fn-scc-octet-listp take nthcdr))))))
(local
 (defthm r6t-segment-true
 (implies (r6t-segmentp x) (true-listp x))
 :hints (("Goal" :in-theory (enable r6t-segmentp)))))
(local
 (defthm r6t-scan-is-admit
 (implies (and (r6t-segmentsp segs) (natp total))
  (equal (r6t-scan (fn-scc-concat segs) total sb fb)
         (if (natp (fn-cth-admit-run segs total sb fb))
             (fn-cth-admit-run segs total sb fb) :refused)))
 :hints (("Goal" :induct (fn-cth-admit-run segs total sb fb)
 :in-theory (union-theories
   '(fn-cth-admit-run fn-scc-concat r6t-segmentsp r6t-segment-scan r6t-segment-admit r6t-scan-nil r6t-segment-true r6t-true-fix
     natp nfix zp r6-nth-cons car-cons cdr-cons (:type-prescription len))
   (theory 'minimal-theory))))))
(local
 (defthm r6t-canonical-frame
 (implies (and (fn-scc-octet-listp chunk) (fn-scc-octet-listp prev)
                (< (len chunk) *fn-scc-u64-bound*))
  (r6t-segmentp (append (fn-scc-header i count (len chunk) s) chunk
                        (fn-scc-seal prev (fn-scc-header i count (len chunk) s) chunk))))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (r6t-segmentp fn-sccr-parse-header-of-append)
                 (fn-scc-parse-header fn-scc-header fn-scc-seal fn-scc-octet-listp))))))
(local
 (defun r6t-chunksp (xs)
 (if (consp xs) (and (r6t-payloadp (car xs)) (r6t-chunksp (cdr xs))) t)))
(local
 (defthm r6t-chunks-good
 (implies (r6t-payloadp payload) (r6t-chunksp (fn-scc-chunks payload seg)))
 :hints (("Goal" :induct (fn-scc-chunks payload seg)
 :in-theory (e/d (fn-scc-chunks r6t-payloadp r6t-chunksp)
                 (fn-scc-octet-listp take nthcdr))))))
(local
 (defthm r6t-frames-good
 (implies (and (r6t-chunksp chunks) (fn-scc-octet-listp prev))
  (r6t-segmentsp (fn-scc-frames chunks index count sequence prev)))
 :hints (("Goal" :induct (fn-scc-frames chunks index count sequence prev)
 :in-theory (union-theories
  '(fn-scc-frames r6t-chunksp r6t-payloadp r6t-segmentsp r6t-canonical-frame r6-header-shape r6-seal-facts
    car-cons cdr-cons (:type-prescription len) natp)
  (theory 'minimal-theory))))))
(local
 (defthm r6t-segments-append
 (equal (r6t-segmentsp (append x y)) (and (r6t-segmentsp x) (r6t-segmentsp y)))
 :hints (("Goal" :induct (binary-append x y)
 :in-theory (union-theories '(binary-append r6t-segmentsp car-cons cdr-cons) (theory 'minimal-theory))))))
(local
 (defthm r6t-run-segments-good
 (implies (r6t-payloadp prog) (r6t-segmentsp (fn-sct-run-segments prog seg s)))
 :hints (("Goal" :in-theory (union-theories '(fn-sct-run-segments r6t-frames-good r6t-chunks-good
                                            (:executable-counterpart fn-scc-octet-listp))
                                           (theory 'minimal-theory))))))
(local
 (defthm r6t-file-segments-good
 (implies (fn-sct-programs-widthp progs) (r6t-segmentsp (fn-sct-file-segments progs seg s)))
 :hints (("Goal" :in-theory (union-theories
  '(fn-sct-programs-widthp fn-sct-programsp fn-sct-file-segments r6t-segments-append r6t-run-segments-good
    r6t-payloadp (:type-prescription len)) (theory 'minimal-theory))))))
(local
 (defthm r6t-candidate-without-trie
   (equal (fn-sct-candidate x nil n table) nil)
   :hints (("Goal" :in-theory (enable fn-sct-candidate fn-cei-trie-records)))))
(local
 (defthm r6t-program-table-irrelevant
   (implies (syntaxp (not (equal table ''nil)))
            (equal (fn-sct-program x nil nil n table) (fn-sct-program x nil nil n nil)))
   :hints (("Goal" :induct (fn-sct-program x nil nil n table)
            :in-theory (e/d (fn-sct-program)
                            (fn-scc-program fn-scc-atom-octets fn-sct-refp
                             fn-scc-octets-valuep))))))
(local
 (defthm r6t-rows-program-table-irrelevant
   (implies (syntaxp (not (equal table ''nil)))
            (equal (fn-sct-rows-program rows i nil nil n table)
                   (fn-sct-rows-program rows i nil nil n nil)))
   :hints (("Goal" :in-theory (e/d (fn-sct-rows-program) (fn-sct-program))))))
(local
 (defthm r6t-setup-fields
 (let* ((tables (fn-sct-tables-of-capture next frontier revision log))
        (index (fn-sco-event-index next))
        (setup (fn-cth-publication-setup next frontier revision log seg profile cfg free alen hlen)))
  (implies (fn-ockp-tables-encodablep tables)
   (and (equal (nth 1 setup) tables)
        (equal (nth 2 setup) (fn-ockp-counts tables index seg))
        (equal (nth 3 setup) (fn-cei-msgid-trie index))
        (equal (nth 4 setup) index)
        (equal (nth 5 setup) (len (fn-sct-tables-e tables))))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories
   '(fn-cth-publication-setup fn-scka-publication-setup fn-ockp-setup fn-sco-at
     nth update-nth zp car-cons cdr-cons nfix (:type-prescription len))
   (theory 'minimal-theory))))))
(local
 (defthm r6t-initial-shape
 (equal (fn-cth-table-initial-state tables total fn-octets)
        (list 0 (fn-ockp-table-rows tables 0) 0 0 *fn-scc-genesis* (len fn-octets) total))
 :hints (("Goal" :in-theory (union-theories
   '(fn-cth-table-initial-state fn-ockp-initial-state fn-oct-len-is-len update-nth zp car-cons cdr-cons)
   (theory 'minimal-theory))))))
(local
 (defthm r6t-start-invp
 (let* ((setup (fn-cth-publication-setup next frontier revision log seg profile cfg free alen hlen))
        (tables (fn-sct-tables-of-capture next frontier revision log))
        (progs (fn-sct-table-programs tables (fn-sco-event-index next))))
  (implies (and (natp t1) (fn-ockp-tables-encodablep tables) (fn-sct-programs-widthp progs)
                (true-listp fn-octets))
   (r6t-loop-invp setup (fn-cth-table-initial-state tables t1 fn-octets) fn-octets)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories
  '(r6t-loop-invp r6t-invp r6t-later-good-unfold r6t-later-done r6t-payloadp r6t-setup-fields r6t-initial-shape
    fn-sct-programs-widthp fn-sct-programsp fn-sct-table-programs fn-ockp-table-rows fn-sco-at
    r6t-rows-program-table-irrelevant r6t-nthcdr-at-fill binary-append
    r6-nth-cons r6-nth-zero car-cons cdr-cons natp nfix zp (:type-prescription len)
    (:executable-counterpart fn-scc-octet-listp))
  (set-difference-theories (theory 'minimal-theory) '(nth)))))))
(local
 (defthm r6t-ockp-later-done
   (implies (or (not (natp k)) (>= k 4))
            (equal (fn-ockp-later tables k n mtrie table counts seg s) nil))
   :hints (("Goal" :in-theory (enable fn-ockp-later)))))
(local
 (defthm r6t-ockp-later-unfold
   (implies (and (natp k) (< k 4))
            (equal (fn-ockp-later tables k n mtrie table counts seg s)
                   (append (fn-ockp-run-remaining (fn-ockp-table-rows tables k) 0 (eql k 2)
                                                  (if (eql k 3) mtrie nil) n table
                                                  0 (fn-ockp-count counts k) s *fn-scc-genesis*
                                                  0 seg nil)
                           (fn-ockp-later tables (+ 1 k) n mtrie table counts seg s))))
   :hints (("Goal" :expand ((fn-ockp-later tables k n mtrie table counts seg s))))))
(local
 (defthm r6t-concat-append
 (equal (fn-scc-concat (append a b)) (append (fn-scc-concat a) (fn-scc-concat b)))
 :hints (("Goal" :induct (binary-append a b)
 :in-theory (union-theories '(binary-append fn-scc-concat r6t-append-assoc car-cons cdr-cons)
                            (theory 'minimal-theory))))))
(local
 (defthm r6t-remaining-is-file
 (implies (and (true-listp buf) (fn-sct-tables-treep tables))
  (equal (fn-ockp-remaining tables 0 (fn-ockp-table-rows tables 0) 0 0 *fn-scc-genesis* (len buf)
                            (len (fn-sct-tables-e tables)) (fn-cei-msgid-trie index) index
                            (fn-ockp-counts tables index seg) seg s buf)
         (fn-sct-file-octets (fn-sct-table-programs tables index) seg s)))
 :hints (("Goal" :do-not-induct t
 :in-theory (e/d (fn-ockp-remaining fn-ockp-run-remaining r6t-ockp-later-unfold r6t-ockp-later-done
                  fn-sct-file-octets fn-sct-file-segments fn-sct-run-segments fn-sct-table-programs
                  fn-ockp-table-rows fn-ockp-count fn-sco-at fn-ockp-counts-are-chunk-counts)
                 (fn-scc-chunks fn-scc-frames fn-scc-concat fn-sct-rows-program
                  fn-ockp-counts fn-cei-msgid-trie fn-ockp-later nthcdr))))))
(local
 (defthm r6t-publication-output
 (let* ((setup (fn-cth-publication-setup next frontier revision log seg profile cfg free alen hlen))
        (tables (fn-sct-tables-of-capture next frontier revision log))
        (run (fn-ockp-run setup (fn-cth-table-initial-state tables t1 fn-octets)
                           b bytes seg s sb fb fuel fn-octets)))
  (implies (and (fn-ockp-tables-encodablep tables) (true-listp fn-octets) (natp seg)
                (equal (mv-nth 0 run) :ok))
   (equal (mv-nth 1 run)
          (fn-sct-file-octets (fn-sct-table-programs tables (fn-sco-event-index next)) seg s))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-ockp-run-is-the-remaining
          (setup (fn-cth-publication-setup next frontier revision log seg profile cfg free alen hlen))
          (pst (fn-cth-table-initial-state (fn-sct-tables-of-capture next frontier revision log) t1 fn-octets))
          (segment-bound sb) (file-bound fb)))
 :in-theory (union-theories
   '(r6t-initial-shape r6t-setup-fields fn-sco-at r6t-remaining-is-file fn-ockp-tables-encodablep-treep
     natp nfix zp r6-nth-cons r6-mv-cons r6-mv-zero car-cons cdr-cons (:type-prescription len))
   (set-difference-theories (theory 'minimal-theory) '(nth mv-nth)))))))
(defthm fn-cth-table-write-is-admitted
 (let* ((setup (fn-cth-publication-setup next frontier revision log seg profile cfg free alen hlen))
         (tables (fn-sct-tables-of-capture next frontier revision log))
         (progs (fn-sct-table-programs tables (fn-sco-event-index next)))
         (run (fn-ockp-run setup (fn-cth-table-initial-state tables t1 fn-octets)
                           b bytes seg s segment-bound file-bound fuel fn-octets)))
    (implies (and (natp t1)
                  (fn-ockp-tables-encodablep tables)
                  (fn-sct-programs-widthp progs)
                  (true-listp fn-octets) (natp seg)
                  (equal (mv-nth 0 run) :ok))
             (equal (fn-cth-admit-run (fn-sct-file-segments progs seg s) t1 segment-bound file-bound)
                    (+ t1 (len (mv-nth 1 run))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance r6t-run-scan
          (setup (fn-cth-publication-setup next frontier revision log seg profile cfg free alen hlen))
          (pst (fn-cth-table-initial-state (fn-sct-tables-of-capture next frontier revision log) t1 fn-octets))
          (sb segment-bound) (fb file-bound))
       (:instance r6t-start-invp)
       (:instance r6t-publication-output (sb segment-bound) (fb file-bound))
       (:instance r6t-scan-is-admit
          (segs (fn-sct-file-segments
                  (fn-sct-table-programs (fn-sct-tables-of-capture next frontier revision log)
                                         (fn-sco-event-index next)) seg s))
          (total t1) (sb segment-bound) (fb file-bound)))
 :in-theory (union-theories
   '(r6t-file-segments-good fn-sct-file-octets r6t-initial-shape
     natp nfix zp r6-nth-cons r6-mv-cons r6-mv-zero car-cons cdr-cons (:type-prescription len))
   (set-difference-theories (theory 'minimal-theory) '(nth mv-nth))))))
)
