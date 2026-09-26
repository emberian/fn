; Witnesses and teeth for books/store-compact-verb.
(in-package "ACL2")
(include-book "../../books/store-compact-verb")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

; A reachable five-event history (the one checkpoint-compaction-preservation
; tests): a record, an undertaking, its release, an identity event and an
; enrollment, at txids 0..4 under frontier 6.
(defconst *cvt-a0*
  (fn-record-make 0 0 0 "<compact@example.invalid>" '(65 13 10)
                  '("fn.letters") "archive-0" "subject-0" "evidence-0" 3 841000000))
(defconst *cvt-e1*
  (fn-store-retention-event-make :undertake 1 1 1
                                 "forward-1" "subject-1" "evidence-1" 2))
(defconst *cvt-e2*
  (fn-store-retention-event-make :release 2 2 2
                                 "forward-1" "subject-1" "receipt-1" 0))
(defconst *cvt-i3*
  (fn-stxe-make 3 3 3 "<compact@example.invalid>" :unverified
                '(117 110 118 101 114 105 102 105 101 100) 7 '(116 101 115 116)))
(defconst *cvt-k4*
  (fn-stxk-make 4 4 4 7 '(116 101 115 116) '(1 2 3 4)))
(make-event `(defconst *cvt-records*
               ',(list (fn-store-event-encode *cvt-a0*)
                       (fn-store-event-encode *cvt-e1*)
                       (fn-store-event-encode *cvt-e2*)
                       (fn-store-event-encode *cvt-i3*)
                       (fn-store-event-encode *cvt-k4*))))
(make-event `(defconst *cvt-names*
               ',(list (fn-bs-txn-name 0) (fn-bs-txn-name 1) (fn-bs-txn-name 2)
                       (fn-bs-txn-name 3) (fn-bs-txn-name 4))))
(defconst *cvt-dev* *fn-bs-profile-development*)
; PKT-169: the free octets the host observed on the store's filesystem.
(defconst *cvt-disk* 1000000)

(assert-event (fn-cc-octet-event-listp *cvt-records* 0 0 6))

; Reachable, non-degenerate: a fresh development store with five
; transaction files and no pack packs, selects, reclaims and retires.  The
; pack the capture produces fits the disk's free octets.
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 0 *cvt-names* nil nil *cvt-disk*)
        (list :compact *fn-cverb-pack-steps*)))
(assert-event (equal (car (fn-cc-capture *cvt-records* 6)) :ok))
(assert-event
 (<= (+ (len (fn-cc-encode (fn-cc-nth 1 (fn-cc-capture *cvt-records* 6))))
        *fn-frame-trailer-octets*)
     *cvt-disk*))
; The accounted pack octets are an upper bound of the real payload, and
; close to it: the real encoding is at most 32 + 5 per event smaller.
(assert-event
 (let ((real (len (fn-cc-encode (fn-cc-nth 1 (fn-cc-capture *cvt-records* 6)))))
       (accounted (fn-cc-event-octets-size *cvt-records*)))
   (and (<= real accounted) (<= accounted (+ real 32 25)))))

; Resume: after a cut at or after the selection (pack generation 1 selected,
; generation 0 an older one) the verb reclaims and retires and writes no
; pack; once both are done it is refused as already compact.
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 5 *cvt-names* '(0 1) 1 nil)
        (list :compact *fn-cverb-resume-steps*)))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 5 nil '(0 1) 1 nil)
        (list :compact *fn-cverb-resume-steps*)))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 5 *cvt-names* '(1) 1 nil)
        (list :compact *fn-cverb-resume-steps*)))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 5 nil '(1) 1 nil)
        '(:refused :already-compact)))
; A partly compacted store with new records past the pack packs again.
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 3
                         (list (fn-bs-txn-name 3) (fn-bs-txn-name 4)) '(0) 0 *cvt-disk*)
        (list :compact *fn-cverb-pack-steps*)))
; The other refusals, each by name.
(assert-event (equal (fn-cverb-decide *cvt-dev* nil 0 nil nil nil nil)
                     '(:refused :empty-history)))
(assert-event (equal (fn-cverb-decide '(7 1 2 3 4 5) *cvt-records* 0 *cvt-names* nil nil nil)
                     '(:refused :profile)))
(assert-event (equal (fn-cverb-decide *cvt-dev* *cvt-records* 6 *cvt-names* nil nil nil)
                     '(:refused :observation)))

; Temporary space (PKT-169, over the link): the same store on a disk one
; octet short of the link file the host seals is refused before a byte is
; written; so is a store whose free space the host could not observe; at
; exactly the link's accounted octets it packs.  The history bound H is not
; read: F2's tight store (files beside the pack past H) packs when the disk
; has room.  (Macros: the capture calls the record codec's attachment, which
; a defconst may not evaluate.)
(defmacro cvt-link-file (records lower lf gen digest)
  `(+ (len (fn-ccc-encode-link
            (cadr (fn-ccc-capture-link ,records ,lower ,lf ,gen ,digest))))
      *fn-frame-trailer-octets*))
(defmacro cvt-pack-file () '(cvt-link-file *cvt-records* 0 0 0 nil))
(defmacro cvt-small () '(1- (cvt-pack-file)))
(assert-event (< 0 (len (fn-ccc-encode-link
                         (cadr (fn-ccc-capture-link *cvt-records* 0 0 0 nil))))))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 0 *cvt-names* nil nil (cvt-small))
        '(:refused :temporary-space)))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 0 *cvt-names* nil nil nil)
        '(:refused :temporary-space)))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 0 *cvt-names* nil nil
                         (fn-cverb-link-octets *cvt-records* 0))
        (list :compact *fn-cverb-pack-steps*)))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 0 *cvt-names* nil nil
                         (1- (fn-cverb-link-octets *cvt-records* 0)))
        '(:refused :temporary-space)))
; The accounted link octets are an upper bound of the link file, and close
; to it: the header bound and the per-event heads.
(assert-event
 (let ((real (cvt-pack-file)) (accounted (fn-cverb-link-octets *cvt-records* 0)))
   (and (<= real accounted) (<= accounted (+ real 128 32 25)))))
; Reachable witness of fn-cverb-pack-fits-the-disk at its boundary: the
; decision packs at exactly the accounted octets, and the link the host
; seals above a chain boundary (lower 1, a 32-octet predecessor digest)
; fits them.
(defconst *cvt-digest-32* (make-list 32 :initial-element 7))
(assert-event
 (equal (fn-cverb-decide *cvt-dev* *cvt-records* 1 (cdr *cvt-names*) '(0) 0
                         (fn-cverb-link-octets *cvt-records* 1))
        (list :compact *fn-cverb-pack-steps*)))
(assert-event (equal (car (fn-ccc-capture-link *cvt-records* 1 1 0 *cvt-digest-32*)) :ok))
(assert-event (<= (cvt-link-file *cvt-records* 1 1 0 *cvt-digest-32*)
                  (fn-cverb-link-octets *cvt-records* 1)))
; The keystone has no hypothesis on the digest: a predecessor digest longer
; than a frame trailer is not encoded (the bounded encoder writes nothing for
; it), so the file stays within the accounting.  Finding for PKT-332: the
; capture accepts such a digest although the link then does not name its
; predecessor; the host always hands it the 32-octet frame trailer.
(defconst *cvt-digest-200* (make-list 200 :initial-element 7))
(assert-event (equal (car (fn-ccc-capture-link *cvt-records* 1 1 0 *cvt-digest-200*)) :ok))
(assert-event (<= (cvt-link-file *cvt-records* 1 1 0 *cvt-digest-200*)
                  (fn-cverb-link-octets *cvt-records* 1)))
; Tooth (the decision, the keystone's one hypothesis): without the pack
; decision the conclusion fails on the short disk.
(local
 (must-fail
  (defthm cvt-disk-without-decision
    (<= (cvt-pack-file) (cvt-small)))))
;; No compaction unit (P5, chained packs): a 4097-event history, one over a
;; link's event quantum, is packed; the first link takes the quantum and the
;; second the one record left.
(defun cvt-many (i n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil
    (cons (fn-store-event-encode
           (fn-record-make i i i "<many@example.invalid>" '(65)
                           '("fn.letters") "a" "s" "e" 1 841000000))
          (cvt-many (1+ i) (1- n)))))
(make-event `(defconst *cvt-4097* ',(cvt-many 0 4097)))
(assert-event (equal (fn-cverb-decide *cvt-dev* *cvt-4097* 0 nil nil nil *cvt-disk*)
                     (list :compact *fn-cverb-pack-steps*)))
;; The disk is asked for one link (one quantum), not the history: at the
;; first link's accounted octets (the 4096 events it takes) the 4097-event
;; history packs; the second decision, above the first link, asks for the
;; one record left.
(assert-event (equal (fn-cverb-decide *cvt-dev* *cvt-4097* 0 nil nil nil
                                      (fn-cverb-link-octets *cvt-4097* 0))
                     (list :compact *fn-cverb-pack-steps*)))
(assert-event (equal (fn-cverb-link-octets *cvt-4097* 0)
                     (+ 128 (fn-cc-event-octets-size (take 4096 *cvt-4097*)) 32)))
(assert-event (equal (fn-cverb-link-octets *cvt-4097* 4096)
                     (+ 128 (fn-cc-event-octets-size (nthcdr 4096 *cvt-4097*)) 32)))
(make-event `(defconst *cvt-link-1* ',(fn-ccc-capture-link *cvt-4097* 0 0 0 nil)))
(assert-event (equal (car *cvt-link-1*) :ok))
(assert-event (equal (fn-ccc-boundary (cadr *cvt-link-1*)) *fn-cc-max-events*))
(assert-event (equal (car (fn-ccc-capture-link *cvt-4097* 4096
                                               (fn-ccc-frontier (cadr *cvt-link-1*))
                                               0 '(1 2 3)))
                     :ok))

;; Teeth for fn-cverb-pack-decision-capture-succeeds.  Reachable: the five
;; events, decided and captured whole (every other hypothesis holds).
(assert-event (equal (fn-cverb-decide *cvt-dev* *cvt-records* 0 *cvt-names* nil nil
                                      *cvt-disk*)
                     (list :compact *fn-cverb-pack-steps*)))
(assert-event (equal (car (fn-ccc-capture-link *cvt-records* 0 0 0 nil)) :ok))
;; Without the pack decision: a chain already covering all five (lower 5)
;; with the other hypotheses holding (the empty suffix is valid) is refused.
(assert-event (fn-cc-octet-event-listp (nthcdr 5 *cvt-records*) 5 5 6))
(assert-event (not (equal (fn-cverb-decide *cvt-dev* *cvt-records* 5 nil nil nil nil)
                          (list :compact *fn-cverb-pack-steps*))))
(local (must-fail (defthm cvt-capture-without-decision
                    (equal (car (fn-ccc-capture-link *cvt-records* 5 5 0 nil)) :ok))))
;; Without a uint32 frontier: one record at txid 2^32-1 is a valid suffix
;; under frontier 2^32; the link's frontier would be 2^32 and is refused.
(make-event `(defconst *cvt-top*
               ',(list (fn-store-event-encode
                        (fn-record-make 0 4294967295 4294967295 "<top@example.invalid>"
                                        '(65) '("fn.letters") "a" "s" "e" 1 841000000)))))
(assert-event (fn-cc-octet-event-listp *cvt-top* 0 0 4294967296))
(assert-event (not (fn-record-uint32p 4294967296)))
(assert-event (equal (fn-cverb-decide *cvt-dev* *cvt-top* 0 nil nil nil *cvt-disk*)
                     (list :compact *fn-cverb-pack-steps*)))
(local (must-fail (defthm cvt-capture-without-uint32-frontier
                    (equal (car (fn-ccc-capture-link *cvt-top* 0 0 0 nil)) :ok))))
;; Without the valid suffix: bytes that are no Store event are packed by the
;; decision (it reads sizes only) and refused by the capture.
(assert-event
 (equal (fn-cverb-decide *cvt-dev* '((1 2 3)) 0 (list (fn-bs-txn-name 0)) nil nil *cvt-disk*)
        (list :compact *fn-cverb-pack-steps*)))
(local (must-fail (defthm cvt-capture-without-event-list
                    (equal (car (fn-ccc-capture-link '((1 2 3)) 0 0 0 nil)) :ok))))
;; Without a uint32 generation or an octet digest: the link names them.
(local (must-fail (defthm cvt-capture-without-uint32-generation
                    (equal (car (fn-ccc-capture-link *cvt-records* 1 1 4294967296 nil))
                           :ok))))
(assert-event (fn-cc-octet-event-listp (nthcdr 1 *cvt-records*) 1 1 6))
(assert-event (equal (car (fn-ccc-capture-link *cvt-records* 1 1 0 nil)) :ok))
(local (must-fail (defthm cvt-capture-without-octet-digest
                    (equal (car (fn-ccc-capture-link *cvt-records* 1 1 0 '(256)))
                           :ok))))

; Tooth for fn-cverb-preset-count-within-pack-events: a valid operator
; profile that is not a preset -- the D27 defaults -- names more transactions
; than one link holds; the chain then takes more than one link.
(assert-event (fn-bs-profile-validp *fn-bs-profile-defaults*))
(assert-event (< *fn-cc-max-events*
                 (fn-bs-profile-max-transactions *fn-bs-profile-defaults*)))
(local
 (must-fail
  (defthm cvt-count-without-preset
    (implies (fn-bs-profile-validp profile)
             (<= (fn-bs-profile-max-transactions profile) *fn-cc-max-events*)))))
(assert-event (equal (fn-cverb-decide '(7 1048576 32768 805306368 5000 1)
                                      *cvt-records* 0 *cvt-names* nil nil nil)
                     '(:refused :profile)))

; Finding 3.  The newest record lost and the newest reservation abandoned
; are one observation.  The five-event history at frontier 5 and its
; four-event prefix at the same frontier are both admitted by the open's
; history gate; the prefix is also exactly what the store holds when
; record 4's reservation advanced the frontier to 5 and the process died
; before the record was written (books/replay.lisp, a known-aborted gap).
(defconst *cvt-history* (list *cvt-a0* *cvt-e1* *cvt-e2* *cvt-i3* *cvt-k4*))
(assert-event (fn-sn-observed-historyp 5 *cvt-history*))
(assert-event (fn-sn-observed-historyp 5 (list *cvt-a0* *cvt-e1* *cvt-e2* *cvt-i3*)))
; The namespace gate the same: the five names and the four without the
; newest are both valid observations under the development bound.
(assert-event (not (equal (fn-profile-txn-observation *cvt-names* 128 0) :invalid)))
(assert-event (not (equal (fn-profile-txn-observation (butlast *cvt-names* 1) 128 0)
                          :invalid)))
; Tooth for fn-cverb-open-history-gate-admits-a-lost-suffix (true-listp):
; an improper prefix whose append is the one-event history is not admitted.
(local (defthm cvt-improper-prefix-appends-to-one-event
         (equal (append (cons *cvt-a0* 7) nil) (list *cvt-a0*))))
(assert-event (fn-sn-observed-historyp 5 (list *cvt-a0*)))
(local
 (must-fail
  (defthm cvt-gate-without-true-list
    (fn-sn-observed-historyp 5 (cons *cvt-a0* 7)))))
