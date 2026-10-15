; Append and MOVE byte observations over the actual LC encoder and LB readers.
; No catalog correspondence premise or LB routing body is unfolded.
(in-package "ACL2")
(include-book "log-cleaning-move")

(defthm lccm-range-permission-survives-append
 (implies (fn-lb-log-model-range-in-entries offset n entries)
  (fn-lb-log-model-range-in-entries offset n (append entries tail)))
 :hints (("Goal" :induct (len entries) :expand ((fn-lb-log-model-range-in-entries offset n (append entries tail)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-range-in-entries binary-append
 (:induction len) len car-cons cdr-cons)))))

(defthm lccm-take-prefix-of-append
 (implies (and (natp n) (<= n (len before)))
  (equal (take n (append before after)) (take n before)))
 :hints (("Goal" :induct (take n before)
 :in-theory (union-theories (theory 'minimal-theory)
 '(take binary-append len natp nfix (:induction take) endp
 car-cons cdr-cons (:executable-counterpart zp))))))

(defthm lccm-slice-prefix-of-append
 (implies (and (natp offset) (natp n) (<= (+ offset n) (len before)))
  (equal (take n (nthcdr offset (append before after)))
         (take n (nthcdr offset before))))
 :hints (("Goal" :induct (nthcdr offset before)
 :in-theory (union-theories (theory 'minimal-theory)
 '(nthcdr binary-append len natp nfix lccm-take-prefix-of-append
 (:induction nthcdr) endp car-cons cdr-cons (:executable-counterpart zp))))))

(defthm lccm-segment-of-append-prepared
 (implies (fn-lc-segsp segs)
 (equal (fn-lb-log-model-segment query (fn-lc-append-prepared record id unit segs))
  (let ((old (fn-lb-log-model-segment query segs)))
   (if (and old (equal query id))
    (list id
     (append (cadr old) (nth 1 record)
       (fn-bs-zeros (fn-lg-pad-len (len (nth 1 record)) unit)))
     (append (caddr old) (if (nth 2 record) (list (nth 2 record)) nil)))
    old))))
 :hints (("Goal" :induct (fn-lc-append-prepared record id unit segs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-append-prepared fn-lb-log-model-segment fn-lc-segsp fn-lb-log-model-segsp
 (:induction fn-lc-append-prepared) len true-listp nth car-cons cdr-cons
 (:executable-counterpart zp) (:executable-counterpart equal))))))

(defthm lccm-len-append
 (equal (len (append before after)) (+ (len before) (len after)))
 :hints (("Goal" :induct (append before after)
 :in-theory (union-theories (theory 'minimal-theory)
 '(len binary-append (:induction binary-append) car-cons cdr-cons)))))

(defthm lccm-existing-range-survives-prepared
 (implies (and (fn-lc-segsp segs)
               (not (equal (fn-lb-log-model-read-range query offset n segs) :bad)))
  (equal (fn-lb-log-model-read-range query offset n
           (fn-lc-append-prepared record id unit segs))
         (fn-lb-log-model-read-range query offset n segs)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-read-range lccm-segment-of-append-prepared
 lccm-slice-prefix-of-append lccm-range-permission-survives-append
 lccm-len-append (:type-prescription len) car-cons cdr-cons
 (:executable-counterpart equal))))))

(defthm lccm-existing-home-entry-survives-append
 (implies (fn-lb-log-model-home-entry pos entries)
  (equal (fn-lb-log-model-home-entry pos (append entries tail))
         (fn-lb-log-model-home-entry pos entries)))
 :hints (("Goal" :induct (len entries)
 :expand ((fn-lb-log-model-home-entry pos (append entries tail)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-home-entry binary-append len (:induction len) car-cons cdr-cons)))))

(defthm lccm-existing-home-survives-prepared
 (implies (and (fn-lc-segsp segs)
   (not (equal (fn-lb-log-model-read-home-frame position segs) :bad)))
  (equal (fn-lb-log-model-read-home-frame position
           (fn-lc-append-prepared record id unit segs))
         (fn-lb-log-model-read-home-frame position segs)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-read-home-frame lccm-segment-of-append-prepared
 lccm-existing-home-entry-survives-append lccm-existing-range-survives-prepared
 car-cons cdr-cons (:executable-counterpart equal))))))

(defthm lccm-len-take
 (equal (len (take n xs)) (nfix n))
 :hints (("Goal" :induct (take n xs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(take zp len nfix natp (:induction take) endp car-cons cdr-cons
 (:executable-counterpart zp))))))

(defthm lccm-true-listp-take
 (true-listp (take n xs))
 :hints (("Goal" :induct (take n xs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(take zp true-listp nfix natp (:induction take) endp car-cons cdr-cons
 (:executable-counterpart zp))))))

(defthm lccm-move-frame-prev-width
 (implies (fn-lc-move-framep frame prev max)
  (and (equal (len prev) 32) (true-listp prev)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-move-framep lccm-len-take lccm-true-listp-take (:executable-counterpart nfix))))))

(defthm lccm-move-frame-length
 (equal (len (fn-lc-move-frame prev i wire home))
        (+ 54 (len prev) (len wire) (len home)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-move-frame fn-frame-seal fn-frame-encode fn-frame-protected fn-frame-header
 lccm-len-append fn-cbor-u64-bytes-length fn-frame-u32-bytes-len fn-frame-digest-length
 len car-cons cdr-cons (:executable-counterpart len))))))

(defthm lccm-offset-cancel
 (implies (and (natp a) (natp b))
  (equal (+ -1 a 1 b) (+ a b)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(natp)))))

(defthm lccm-nthcdr-append-prefix
 (implies (natp n)
  (equal (nthcdr (+ (len prefix) n) (append prefix suffix)) (nthcdr n suffix)))
 :hints (("Goal" :induct (len prefix) :expand ((:free (k x xs) (nthcdr k (cons x xs))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(nthcdr binary-append len natp nfix zp (:type-prescription len) fold-consts-in-+ associativity-of-+ commutativity-of-+ unicity-of-0 fix lccm-offset-cancel (:induction len) endp
 car-cons cdr-cons (:executable-counterpart zp))))))

(defthm lccm-take-len-is-list-fix
 (equal (take (len xs) xs) (true-list-fix xs))
 :hints (("Goal" :induct (len xs) :expand ((:free (k) (take k xs)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(take zp fold-consts-in-+ unicity-of-0 fix true-list-fix len natp nfix (:type-prescription len) (:induction len) endp
 car-cons cdr-cons (:executable-counterpart zp))))))

(defthm lccm-append-associative
 (equal (append (append a b) c) (append a (append b c)))
 :hints (("Goal" :induct (append a b)
 :in-theory (union-theories (theory 'minimal-theory)
 '(binary-append (:induction binary-append) car-cons cdr-cons)))))

(defthm lccm-move-frame-fragments-by-definition
 (let* ((payload (append prev (fn-cbor-u64-bytes i) (fn-cbor-u32-bytes (len wire)) wire home))
        (prefix (append (fn-frame-header *fn-lg-magic* *fn-lg-version* *fn-lc-move-kind* (len payload))
                       prev (fn-cbor-u64-bytes i) (fn-cbor-u32-bytes (len wire)))))
  (equal (fn-lc-move-frame prev i wire home)
   (append prefix wire home (fn-frame-digest
          (fn-frame-protected *fn-lg-magic* *fn-lg-version* *fn-lc-move-kind* payload)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-move-frame fn-frame-seal fn-frame-encode fn-frame-protected
 lccm-append-associative)))))

(defthm lccm-move-prefix-length
 (equal (len (append
  (fn-frame-header *fn-lg-magic* *fn-lg-version* *fn-lc-move-kind* n)
  prev (fn-cbor-u64-bytes i) (fn-cbor-u32-bytes w)))
  (+ 22 (len prev)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-frame-header lccm-len-append fn-cbor-u64-bytes-length fn-frame-u32-bytes-len
 len car-cons cdr-cons (:executable-counterpart len))))))

(defthm lccm-move-frame-wire-slice
 (equal (take (len wire) (nthcdr (+ 22 (len prev)) (fn-lc-move-frame prev i wire home)))
        (true-list-fix wire))
 :hints (("Goal" :use ((:instance lccm-nthcdr-append-prefix
  (prefix (append (fn-frame-header *fn-lg-magic* *fn-lg-version* *fn-lc-move-kind* (len (append prev (fn-cbor-u64-bytes i) (fn-cbor-u32-bytes (len wire)) wire home))) prev (fn-cbor-u64-bytes i) (fn-cbor-u32-bytes (len wire)))) (suffix (append wire home (fn-frame-digest (fn-frame-protected *fn-lg-magic* *fn-lg-version* *fn-lc-move-kind* (append prev (fn-cbor-u64-bytes i) (fn-cbor-u32-bytes (len wire)) wire home))))) (n 0)))
 :expand ((:free (xs) (nthcdr 0 xs)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-move-frame-fragments-by-definition lccm-move-prefix-length
 lccm-append-associative lccm-len-append lccm-take-prefix-of-append
 lccm-take-len-is-list-fix (:type-prescription len) natp fix unicity-of-0
 associativity-of-+ commutativity-of-+ fold-consts-in-+
 (:executable-counterpart zp) (:executable-counterpart nfix))))))

(defthm lccm-move-long-prefix-length
 (equal (len (append
  (fn-frame-header *fn-lg-magic* *fn-lg-version* *fn-lc-move-kind* n)
  prev (fn-cbor-u64-bytes i) (fn-cbor-u32-bytes w) more))
  (+ 22 (len prev) (len more)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-frame-header lccm-len-append fn-cbor-u64-bytes-length fn-frame-u32-bytes-len
 len car-cons cdr-cons (:executable-counterpart len))))))

(defthm lccm-move-frame-home-slice
 (equal (take (len home) (nthcdr (+ 22 (len prev) (len wire)) (fn-lc-move-frame prev i wire home)))
        (true-list-fix home))
 :hints (("Goal" :use ((:instance lccm-nthcdr-append-prefix
  (prefix (append (append (fn-frame-header *fn-lg-magic* *fn-lg-version* *fn-lc-move-kind* (len (append prev (fn-cbor-u64-bytes i) (fn-cbor-u32-bytes (len wire)) wire home))) prev (fn-cbor-u64-bytes i) (fn-cbor-u32-bytes (len wire))) wire)) (suffix (append home (fn-frame-digest (fn-frame-protected *fn-lg-magic* *fn-lg-version* *fn-lc-move-kind* (append prev (fn-cbor-u64-bytes i) (fn-cbor-u32-bytes (len wire)) wire home))))) (n 0)))
 :expand ((:free (xs) (nthcdr 0 xs)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-move-long-prefix-length lccm-move-frame-fragments-by-definition lccm-move-prefix-length
 lccm-append-associative lccm-len-append lccm-take-prefix-of-append
 lccm-take-len-is-list-fix (:type-prescription len) natp fix unicity-of-0
 associativity-of-+ commutativity-of-+ fold-consts-in-+
 (:executable-counterpart zp) (:executable-counterpart nfix))))))

(defthm lccm-range-permission-in-suffix
 (implies (fn-lb-log-model-range-in-entries offset n tail)
  (fn-lb-log-model-range-in-entries offset n (append entries tail)))
 :hints (("Goal" :induct (len entries)
 :expand ((fn-lb-log-model-range-in-entries offset n (append entries tail)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-range-in-entries binary-append len (:induction len) car-cons cdr-cons)))))

(defthm lccm-prepared-frame-range
 (let* ((old (fn-lb-log-model-segment id segs)) (start (len (cadr old)))
        (absolute (+ start offset)))
  (implies (and (fn-lc-segsp segs) old entry (natp offset) (natp n)
                (<= (+ offset n) (len frame))
                (fn-lb-log-model-range-in-entries absolute n (list entry)))
   (equal (fn-lb-log-model-read-range id absolute n
            (fn-lc-append-prepared (list nil frame entry) id unit segs))
          (take n (nthcdr offset frame)))))
 :hints (("Goal" :use
 ((:instance lccm-nthcdr-append-prefix
   (prefix (cadr (fn-lb-log-model-segment id segs)))
   (suffix (append frame (fn-bs-zeros (fn-lg-pad-len (len frame) unit))))
   (n offset)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-read-range lccm-segment-of-append-prepared
 lccm-range-permission-in-suffix lccm-len-append lccm-slice-prefix-of-append
 natp fix unicity-of-0 associativity-of-+ commutativity-of-+
 (:type-prescription len) nth car-cons cdr-cons
 (:executable-counterpart equal) (:executable-counterpart zp))))))

(defthm lccm-insert-id-membership
 (iff (member-equal id (fn-lc-seg-ids (fn-lc-insert-segment segment segs)))
      (or (equal id (car segment)) (member-equal id (fn-lc-seg-ids segs))))
 :hints (("Goal" :induct (fn-lc-insert-segment segment segs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-insert-segment fn-lc-seg-ids member-equal
 (:induction fn-lc-insert-segment) car-cons cdr-cons)))))

(defthm lccm-ordered-id-membership
 (iff (member-equal id (fn-lc-seg-ids (fn-lc-ordered-segments segs)))
      (member-equal id (fn-lc-seg-ids segs)))
 :hints (("Goal" :induct (fn-lc-ordered-segments segs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-ordered-segments fn-lc-seg-ids member-equal lccm-insert-id-membership
 (:induction fn-lc-ordered-segments) car-cons cdr-cons)))))

(defthm lccm-insert-nonempty
 (consp (fn-lc-insert-segment segment segs))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-insert-segment car-cons cdr-cons)))))

(defthm lccm-ordered-nonempty
 (equal (consp (fn-lc-ordered-segments segs)) (consp segs))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-ordered-segments lccm-insert-nonempty)))))

(defthm lccm-last-id-is-member
 (implies (consp segs)
  (member-equal (fn-lc-last-segment-id segs) (fn-lc-seg-ids segs)))
 :hints (("Goal" :induct (fn-lc-last-segment-id segs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-last-segment-id fn-lc-seg-ids member-equal
 (:induction fn-lc-last-segment-id) car-cons cdr-cons)))))

(defthm lccm-member-id-has-segment
 (implies (and (fn-lc-segsp segs) (member-equal id (fn-lc-seg-ids segs)))
  (fn-lb-log-model-segment id segs))
 :hints (("Goal" :induct (fn-lb-log-model-segment id segs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-segsp fn-lb-log-model-segsp fn-lc-seg-ids fn-lb-log-model-segment
 member-equal len true-listp (:induction fn-lb-log-model-segment) car-cons cdr-cons)))))

(defthm lccm-last-ordered-segment-exists
 (implies (and (fn-lc-segsp segs) (consp segs))
  (fn-lb-log-model-segment
   (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))
 :hints (("Goal" :use
 ((:instance lccm-last-id-is-member (segs (fn-lc-ordered-segments segs))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-ordered-id-membership lccm-ordered-nonempty lccm-member-id-has-segment)))))
