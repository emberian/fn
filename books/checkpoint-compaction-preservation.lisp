; fn: compaction preserves the recovered history (M5).
;
; Compaction in fn is two offline steps over one Store (specs/storage.md,
; "Checkpointing and compaction"):
;
;   1. `checkpoint pack ROOT select' (host/native/checkpoint.lisp
;      `fnn-pack-publish') captures every committed transaction record into
;      one immutable pack (`fn-cc-capture'), publishes it and durably
;      replaces the pack selection marker.
;   2. `checkpoint pack-reclaim ROOT' (`fnn-pack-prefix-reclaim') opens the
;      Store (full recovery, which compares every covered file with the
;      pack), asks ACL2 for the covered names (`fn-bs-pack-reclaim-plan'),
;      unlinks them in order and closes with a transaction-directory barrier.
;
; Opening afterwards (`fnn-recover', host/native/io.lisp) reads the
; namespace through `fn-profile-txn-observation' with the selected pack's
; boundary as the lower bound, reads each surviving file, and hands the
; observed (sequence record) pairs to `fn-ccp-observe-framed' (the body of
; `fn-store-checkpoint-compaction-observe', host/checkpoint-host.lisp),
; whose answer is the one record list given to the generic replay.
;
; This book proves, over those three called functions, that deleting any
; subset of the reclaim plan (every process-death image of the reclaim
; program deletes such a subset; books/byte-store-compaction-correspondence
; proves the uncovered suffix survives each cut byte for byte) leaves the
; namespace observation valid and the reconstructed record list unchanged,
; and that for a complete observation that list is exactly the records read.
; The replayed Store is a function of that list, the frontier and the
; configuration records; reclaim writes none of the three.
(in-package "ACL2")
(include-book "checkpoint-compaction")
(include-book "store-profile-upgrade")
(include-book "byte-store-compaction-correspondence")

(local (in-theory (disable fn-cc-decode-exact)))

; -----------------------------------------------------------------------------
; The framed pack, as the host calls it

(defun fn-ccp-framed-okp (framed digest)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-cbor-octet-listp framed)
       (<= *fn-frame-trailer-octets* (len framed))
       (let ((n (- (len framed) *fn-frame-trailer-octets*)))
         (and (equal (nthcdr n framed) digest)
              (let ((decoded (fn-cc-decode-exact (take n framed))))
                (and (consp decoded) (equal (car decoded) :ok)))))))

(defun fn-ccp-framed-summary (framed digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-ccp-framed-okp framed digest)
      (cadr (fn-cc-decode-exact
             (take (- (len framed) *fn-frame-trailer-octets*) framed)))
    nil))

; The selected pack's coverage boundary: the lower bound the host passes to
; the namespace observation and to the reclaim plan.
(defun fn-ccp-framed-boundary (framed digest)
  (declare (xargs :guard t :verify-guards nil))
  (fn-cc-sequence (fn-ccp-framed-summary framed digest)))

; Called by host/checkpoint-host.lisp `fn-store-checkpoint-compaction-observe'
; (the recovery callback `fnn-pack-recover-records').
(defun fn-ccp-observe-framed (framed digest observed frontier)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((or (not (fn-cbor-octet-listp framed))
             (< (len framed) *fn-frame-trailer-octets*))
         '(:error :frame))
        ((not (fn-ccp-framed-okp framed digest)) '(:error :integrity))
        (t (fn-cc-recover-observation (fn-ccp-framed-summary framed digest)
                                      observed frontier))))

; Called by host/checkpoint-host.lisp `fn-store-checkpoint-compaction-coverage'
; (`fnn-pack-selected-raw-and-coverage', at reclaim and at every open).
(defun fn-ccp-coverage-framed (framed digest observed-count frontier)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((or (not (fn-cbor-octet-listp framed))
             (< (len framed) *fn-frame-trailer-octets*))
         '(:error :frame))
        ((not (fn-ccp-framed-okp framed digest)) '(:error :integrity))
        (t (let ((summary (fn-ccp-framed-summary framed digest)))
             (if (or (< observed-count (fn-cc-sequence summary))
                     (< frontier (fn-cc-frontier summary)))
                 '(:error :coverage)
               (list :ok (fn-cc-sequence summary)
                     (fn-cc-frontier summary)))))))

(defthm fn-ccp-coverage-is-the-framed-boundary-by-definition
  (implies (equal (car (fn-ccp-coverage-framed framed digest count frontier)) :ok)
           (equal (cadr (fn-ccp-coverage-framed framed digest count frontier))
                  (fn-ccp-framed-boundary framed digest))))

(in-theory (disable fn-ccp-framed-okp fn-ccp-framed-summary))

; -----------------------------------------------------------------------------
; What a reclaim leaves: names, pairs, records

(defun fn-ccp-remove-names (names gone)
  (declare (xargs :guard t))
  (if (consp names)
      (if (member-equal (car names) (true-list-fix gone))
          (fn-ccp-remove-names (cdr names) gone)
        (cons (car names) (fn-ccp-remove-names (cdr names) gone)))
    nil))

(defun fn-ccp-remove-pairs (pairs gone)
  (declare (xargs :guard t))
  (if (consp pairs)
      (if (and (consp (car pairs)) (consp (cdar pairs))
               (member-equal (cadar pairs) (true-list-fix gone)))
          (fn-ccp-remove-pairs (cdr pairs) gone)
        (cons (car pairs) (fn-ccp-remove-pairs (cdr pairs) gone)))
    nil))

; The host reads each ACL2-issued (sequence name) pair's file; CONTENTS is
; the bytes each surviving name holds (host/native/io.lisp
; `fnn-durable-records').
(defun fn-ccp-read (pairs contents)
  (declare (xargs :guard (alistp contents)))
  (if (consp pairs)
      (cons (list (if (consp (car pairs)) (caar pairs) nil)
                  (cdr (assoc-equal (if (and (consp (car pairs)) (consp (cdar pairs)))
                                        (cadar pairs) nil)
                                    contents)))
            (fn-ccp-read (cdr pairs) contents))
    nil))

; SUB is WHOLE with some pairs below BOUNDARY left out.
(defun fn-ccp-covered-sublistp (sub whole boundary)
  (declare (xargs :guard t))
  (if (consp whole)
      (or (and (consp sub) (equal (car sub) (car whole))
               (fn-ccp-covered-sublistp (cdr sub) (cdr whole) boundary))
          (and (consp (car whole)) (natp (caar whole)) (rationalp boundary)
               (< (caar whole) boundary)
               (fn-ccp-covered-sublistp sub (cdr whole) boundary)))
    (null sub)))

; -----------------------------------------------------------------------------
; Record level: leaving out covered pairs does not change the answer

(local
 (defthm fn-ccp-sublist-keeps-agreement
   (implies (and (fn-ccp-covered-sublistp sub whole boundary)
                 (fn-cc-observation-agrees whole events boundary))
            (fn-cc-observation-agrees sub events boundary))))

(local
 (defthm fn-ccp-sublist-keeps-suffix
   (implies (fn-ccp-covered-sublistp sub whole boundary)
            (equal (fn-cc-observation-suffix sub boundary)
                   (fn-cc-observation-suffix whole boundary)))))

(defthm fn-ccp-covered-deletion-keeps-reconstruction
  (implies (and (equal (car (fn-ccp-observe-framed framed digest observed frontier))
                       :ok)
                (fn-ccp-covered-sublistp after observed
                                         (fn-ccp-framed-boundary framed digest)))
           (equal (fn-ccp-observe-framed framed digest after frontier)
                  (fn-ccp-observe-framed framed digest observed frontier))))

; -----------------------------------------------------------------------------
; Record level: a complete observation reconstructs exactly the records read

; OBSERVED names sequences N, N+1, ... in order, one record each.
(defun fn-ccp-contiguousp (observed n)
  (declare (xargs :guard t))
  (if (consp observed)
      (and (true-listp (car observed)) (equal (len (car observed)) 2)
           (equal (caar observed) n)
           (fn-ccp-contiguousp (cdr observed) (1+ (nfix n))))
    (null observed)))

(defun fn-ccp-records (observed)
  (declare (xargs :guard t))
  (if (consp observed)
      (cons (if (and (consp (car observed)) (consp (cdar observed)))
                (cadar observed)
              nil)
            (fn-ccp-records (cdr observed)))
    nil))

(local
 (defthm fn-ccp-nthcdr-opens-below-len
   (implies (and (natp n) (< n (len events)))
            (equal (nthcdr n events)
                   (cons (nth n events) (nthcdr (1+ n) events))))))

(local
 (defthm fn-ccp-nthcdr-at-or-past-len
   (implies (and (natp n) (<= (len events) n))
            (not (consp (nthcdr n events))))))

(local
 (defthm fn-ccp-contiguous-agreement-reconstructs
   (implies (and (natp n)
                 (fn-ccp-contiguousp observed n)
                 (fn-cc-observation-agrees observed events (len events))
                 (<= (len events) (+ n (len observed))))
            (equal (append (nthcdr n events)
                           (fn-cc-observation-suffix observed (len events)))
                   (fn-ccp-records observed)))
   :hints (("Goal" :induct (fn-ccp-contiguousp observed n)))))

(defthm fn-ccp-complete-observation-reconstructs-its-records
  (implies (and (equal (car (fn-ccp-observe-framed framed digest observed frontier))
                       :ok)
                (fn-ccp-contiguousp observed 0)
                (<= (fn-ccp-framed-boundary framed digest) (len observed)))
           (equal (fn-ccp-observe-framed framed digest observed frontier)
                  (list :ok (fn-ccp-records observed) frontier)))
  :hints (("Goal"
           :use ((:instance fn-ccp-contiguous-agreement-reconstructs
                            (n 0)
                            (events (fn-cc-events
                                     (fn-ccp-framed-summary framed digest)))))
           :in-theory (enable fn-cc-expand fn-cc-summaryp))))

; -----------------------------------------------------------------------------
; Namespace level: the observation after a reclaim, at any cut

; The names of sequences 0 .. N-1: every name a reclaim plan below N issues.
(defun fn-ccp-names-below (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil
    (cons (fn-bs-txn-name (1- n)) (fn-ccp-names-below (1- n)))))

(local
 (defthm fn-ccp-member-of-subset
   (implies (and (member-equal x a) (subsetp-equal a b))
            (member-equal x b))))

(local
 (defthm fn-ccp-name-at-or-above-is-not-below
   (implies (and (natp k) (natp m) (<= m k))
            (not (member-equal (fn-bs-txn-name k) (fn-ccp-names-below m))))))

(local
 (defthm fn-ccp-name-below-is-below
   (implies (and (natp k) (natp m) (< k m))
            (member-equal (fn-bs-txn-name k) (fn-ccp-names-below m)))))

(local
 (defthm fn-ccp-member-of-removed-names
   (implies (member-equal x (fn-ccp-remove-names names gone))
            (member-equal x names))))

(local
 (defthm fn-ccp-remove-names-len
   (<= (len (fn-ccp-remove-names names gone)) (len names))
   :rule-classes :linear))

; A valid contiguous run from S names nothing below S.
(local
 (defthm fn-ccp-pairs-name-nothing-below
   (implies (and (not (equal (fn-bs-txn-observation-pairs names s) :invalid))
                 (natp k) (natp s) (< k s))
            (not (member-equal (fn-bs-txn-name k) names)))
   :hints (("Goal" :induct (fn-bs-txn-observation-pairs names s)
            :in-theory (enable fn-bs-txn-observation-pairs)))))

(local
 (defthm fn-ccp-covered-name-nothing-below
   (implies (and (not (equal (fn-bs-txn-observation-covered names s lower)
                             :invalid))
                 (natp k) (natp s) (natp lower) (< k s) (<= s lower))
            (not (member-equal (fn-bs-txn-name k) names)))
   :hints (("Goal" :induct (fn-bs-txn-observation-covered names s lower)
            :in-theory (enable fn-bs-txn-observation-covered)))))

(local
 (defthm fn-ccp-covered-name-nothing-below-in-the-rest
   (implies (and (not (equal (fn-bs-txn-observation-covered names s lower)
                             :invalid))
                 (natp k) (natp s) (natp lower) (< k s) (<= s lower))
            (not (member-equal (fn-bs-txn-name k) (cdr names))))
   :hints (("Goal" :use fn-ccp-covered-name-nothing-below
            :in-theory (disable fn-ccp-covered-name-nothing-below)))))

(local
 (defthm fn-ccp-gone-misses-names-at-or-above
   (implies (and (subsetp-equal gone (fn-ccp-names-below m))
                 (natp k) (natp m) (<= m k))
            (not (member-equal (fn-bs-txn-name k) gone)))
   :hints (("Goal" :use ((:instance fn-ccp-member-of-subset
                                    (x (fn-bs-txn-name k)) (a gone)
                                    (b (fn-ccp-names-below m))))
            :in-theory (disable fn-ccp-member-of-subset)))))

(local (in-theory (disable fn-ccp-names-below)))

; The uncovered run is untouched: none of its names is below the boundary.
(local
 (defthm fn-ccp-removal-misses-the-suffix
   (implies (and (not (equal (fn-bs-txn-observation-pairs names s) :invalid))
                 (natp s) (natp lower) (<= lower s)
                 (subsetp-equal gone (fn-ccp-names-below lower)))
            (and (equal (fn-ccp-remove-names names gone) names)
                 (equal (fn-ccp-remove-pairs
                         (fn-bs-txn-observation-pairs names s) gone)
                        (fn-bs-txn-observation-pairs names s))))
   :hints (("Goal" :induct (fn-bs-txn-observation-pairs names s)
            :in-theory (enable fn-bs-txn-observation-pairs)))))

(local
 (defthm fn-ccp-not-member-of-removed-names
   (implies (not (member-equal x names))
            (not (member-equal x (fn-ccp-remove-names names gone))))))

; The covered observation's three shapes, so the commutation below never
; opens it on both sides at once.
(local
 (defthm fn-ccp-covered-skips-an-absent-name
   (implies (and (natp s) (natp lower) (< s lower)
                 (not (member-equal (fn-bs-txn-name s) names)))
            (equal (fn-bs-txn-observation-covered names s lower)
                   (fn-bs-txn-observation-covered names (+ 1 s) lower)))
   :hints (("Goal" :expand ((fn-bs-txn-observation-covered names s lower))))))

(local
 (defthm fn-ccp-covered-takes-a-present-name
   (implies (and (natp s) (natp lower) (< s lower) (consp names)
                 (equal (car names) (fn-bs-txn-name s))
                 (not (equal (fn-bs-txn-observation-covered
                              (cdr names) (+ 1 s) lower)
                             :invalid)))
            (equal (fn-bs-txn-observation-covered names s lower)
                   (cons (list s (car names))
                         (fn-bs-txn-observation-covered
                          (cdr names) (+ 1 s) lower))))
   :hints (("Goal" :expand ((fn-bs-txn-observation-covered names s lower))))))

(local
 (defthm fn-ccp-covered-at-the-boundary
   (implies (and (natp s) (natp lower) (<= lower s))
            (equal (fn-bs-txn-observation-covered names s lower)
                   (fn-bs-txn-observation-pairs names lower)))
   :hints (("Goal" :expand ((fn-bs-txn-observation-covered names s lower))))))

(local
 (defun fn-ccp-covered-induction (names s lower)
   (declare (xargs :measure (nfix (- (nfix lower) (nfix s)))))
   (if (and (natp s) (natp lower) (< s lower))
       (if (and (consp names) (equal (car names) (fn-bs-txn-name s)))
           (fn-ccp-covered-induction (cdr names) (+ 1 s) lower)
         (fn-ccp-covered-induction names (+ 1 s) lower))
     (list names s lower))))

(local
 (defthm fn-ccp-covered-invalid-steps
   (implies (and (natp s) (natp lower) (< s lower)
                 (not (equal (fn-bs-txn-observation-covered names s lower)
                             :invalid)))
            (if (and (consp names) (equal (car names) (fn-bs-txn-name s)))
                (not (equal (fn-bs-txn-observation-covered
                             (cdr names) (+ 1 s) lower)
                            :invalid))
              (not (equal (fn-bs-txn-observation-covered names (+ 1 s) lower)
                          :invalid))))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-bs-txn-observation-covered names s lower))))))

(local
 (defthm fn-ccp-removal-commutes-with-covered-observation
   (implies (and (natp s) (natp lower) (<= s lower)
                 (not (equal (fn-bs-txn-observation-covered names s lower)
                             :invalid))
                 (subsetp-equal gone (fn-ccp-names-below lower)))
            (equal (fn-bs-txn-observation-covered
                    (fn-ccp-remove-names names gone) s lower)
                   (fn-ccp-remove-pairs
                    (fn-bs-txn-observation-covered names s lower) gone)))
   :hints (("Goal" :induct (fn-ccp-covered-induction names s lower)
            :in-theory (disable fn-bs-txn-observation-covered))
           ("Subgoal *1/3"
            :use ((:instance fn-ccp-covered-invalid-steps)
                  (:instance fn-ccp-covered-name-nothing-below
                             (k s) (s (+ 1 s)) (names (cdr names)))
                  (:instance fn-ccp-covered-name-nothing-below
                             (k s) (s (+ 1 s)))))
           ("Subgoal *1/2"
            :use ((:instance fn-ccp-covered-invalid-steps)
                  (:instance fn-ccp-covered-name-nothing-below
                             (k s) (s (+ 1 s)) (names (cdr names)))
                  (:instance fn-ccp-covered-name-nothing-below
                             (k s) (s (+ 1 s)))))
           ("Subgoal *1/1"
            :use ((:instance fn-ccp-covered-invalid-steps)
                  (:instance fn-ccp-covered-name-nothing-below
                             (k s) (s (+ 1 s)) (names (cdr names)))
                  (:instance fn-ccp-covered-name-nothing-below
                             (k s) (s (+ 1 s))))))))

(local
 (defthm fn-ccp-covered-names-of-a-suffix-run
   (implies (and (natp s) (natp lower) (<= lower s))
            (equal (fn-bs-pack-covered-names
                    (fn-bs-txn-observation-pairs names s) lower)
                   nil))
   :hints (("Goal" :expand ((fn-bs-txn-observation-pairs names s))
            :in-theory (enable fn-bs-pack-covered-names)))))

(local
 (defthm fn-ccp-plan-names-are-below
   (implies (and (natp s) (natp lower) (<= s lower)
                 (not (equal (fn-bs-txn-observation-covered names s lower)
                             :invalid)))
            (subsetp-equal (fn-bs-pack-covered-names
                            (fn-bs-txn-observation-covered names s lower)
                            lower)
                           (fn-ccp-names-below lower)))
   :hints (("Goal" :induct (fn-bs-txn-observation-covered names s lower)
            :in-theory (enable fn-bs-txn-observation-covered
                               fn-bs-pack-covered-names)))))

(local
 (defthm fn-ccp-reclaim-plan-names-are-below
   (implies (not (equal (fn-bs-pack-reclaim-plan names maximum lower) :invalid))
            (subsetp-equal (fn-bs-pack-reclaim-plan names maximum lower)
                           (fn-ccp-names-below lower)))
   :hints (("Goal" :in-theory (enable fn-bs-pack-reclaim-plan
                                      fn-profile-txn-observation
                                      fn-bs-txn-observation-selected)))))

(local
 (defthm fn-ccp-subsetp-transitive
   (implies (and (subsetp-equal a b) (subsetp-equal b c))
            (subsetp-equal a c))))

; Every process-death image of the reclaim deletes a subset GONE of the plan.
; The next open's namespace observation (the gate the host calls) is valid
; and is the old observation with exactly GONE's pairs left out.
(defthm fn-ccp-reclaim-keeps-namespace-observation
  (let ((before (fn-profile-txn-observation names maximum lower)))
    (implies (and (not (equal before :invalid))
                  (subsetp-equal gone (fn-bs-pack-reclaim-plan names maximum lower)))
             (equal (fn-profile-txn-observation
                     (fn-ccp-remove-names names gone) maximum lower)
                    (list :ok lower (fn-ccp-remove-pairs (third before) gone)))))
  :hints (("Goal"
           :use ((:instance fn-ccp-reclaim-plan-names-are-below))
           :in-theory (e/d (fn-profile-txn-observation
                            fn-bs-txn-observation-selected)
                           (fn-ccp-reclaim-plan-names-are-below)))))

; The records the host reads after a reclaim are the records it read before
; with only covered pairs left out.
(local
 (defthm fn-ccp-covered-sublist-reflexive
   (implies (true-listp x)
            (fn-ccp-covered-sublistp x x boundary))))

(local
 (defthm fn-ccp-read-true-listp
   (true-listp (fn-ccp-read pairs contents))))

(local
 (defthm fn-ccp-removed-read-is-a-covered-sublist
   (implies (and (natp s) (natp lower) (<= s lower)
                 (not (equal (fn-bs-txn-observation-covered names s lower)
                             :invalid))
                 (subsetp-equal gone (fn-ccp-names-below lower)))
            (fn-ccp-covered-sublistp
             (fn-ccp-read (fn-ccp-remove-pairs
                           (fn-bs-txn-observation-covered names s lower) gone)
                          contents)
             (fn-ccp-read (fn-bs-txn-observation-covered names s lower)
                          contents)
             lower))
   :hints (("Goal" :induct (fn-ccp-covered-induction names s lower)
            :in-theory (disable fn-bs-txn-observation-covered))
           ("Subgoal *1/2" :use ((:instance fn-ccp-covered-invalid-steps)))
           ("Subgoal *1/1" :use ((:instance fn-ccp-covered-invalid-steps))))))

; -----------------------------------------------------------------------------
; The composition: reclaim at any cut, then open

; NAMES is the transaction namespace the reclaim observed (and the open
; before it); LOWER the selected pack's boundary; GONE the planned names a
; process-death image has lost; CONTENTS the bytes of every surviving name
; (unchanged for the uncovered suffix at every cut:
; fn-bs-selected-reclaim-crash-preserves-suffix-payload).  If the open
; before the reclaim reconstructed its history, the open after it observes a
; valid namespace and reconstructs the identical record list.
(defthm fn-ccp-reclaim-preserves-reconstructed-history
  (let* ((before (fn-profile-txn-observation names maximum lower))
         (after (fn-profile-txn-observation
                 (fn-ccp-remove-names names gone) maximum lower)))
    (implies (and (not (equal before :invalid))
                  (subsetp-equal gone
                                 (fn-bs-pack-reclaim-plan names maximum lower))
                  (equal lower (fn-ccp-framed-boundary framed digest))
                  (equal (car (fn-ccp-observe-framed
                               framed digest
                               (fn-ccp-read (third before) contents)
                               frontier))
                         :ok))
             (and (not (equal after :invalid))
                  (equal (fn-ccp-observe-framed
                          framed digest (fn-ccp-read (third after) contents)
                          frontier)
                         (fn-ccp-observe-framed
                          framed digest (fn-ccp-read (third before) contents)
                          frontier)))))
  :hints (("Goal"
           :use ((:instance fn-ccp-reclaim-plan-names-are-below)
                 (:instance fn-ccp-removed-read-is-a-covered-sublist (s 0))
                 (:instance fn-ccp-covered-deletion-keeps-reconstruction
                            (observed (fn-ccp-read
                                       (third (fn-profile-txn-observation
                                               names maximum lower))
                                       contents))
                            (after (fn-ccp-read
                                    (fn-ccp-remove-pairs
                                     (third (fn-profile-txn-observation
                                             names maximum lower))
                                     gone)
                                    contents))))
           :in-theory (e/d (fn-profile-txn-observation
                            fn-bs-txn-observation-selected)
                           (fn-ccp-reclaim-plan-names-are-below
                            fn-ccp-removed-read-is-a-covered-sublist
                            fn-ccp-covered-deletion-keeps-reconstruction
                            fn-ccp-observe-framed
                            fn-ccp-framed-boundary)))))

; -----------------------------------------------------------------------------
; One owner of the namespace bound: the reclaim plan and the coverage check
; read the profile's max_transactions the way the open path does, so an offline
; profile upgrade keeps both answers.

(defthm fn-ccp-profile-upgrade-keeps-reclaim-plan
  (implies (and (fn-profile-upgradep old new)
                (not (equal (fn-bs-pack-reclaim-plan
                             names (fn-bs-profile-max-transactions old) lower)
                            :invalid)))
           (equal (fn-bs-pack-reclaim-plan names (fn-bs-profile-max-transactions new) lower)
                  (fn-bs-pack-reclaim-plan names (fn-bs-profile-max-transactions old) lower)))
  :hints (("Goal" :use ((:instance fn-profile-upgrade-keeps-txn-observation
                                   (selected-lower lower)))
           :in-theory (e/d (fn-bs-pack-reclaim-plan)
                           (fn-profile-upgrade-keeps-txn-observation
                            fn-bs-profile-max-transactions
                            fn-profile-upgradep fn-profile-txn-observation)))))

(defthm fn-ccp-larger-count-keeps-coverage
  (implies (and (equal (car (fn-ccp-coverage-framed framed digest old frontier))
                       :ok)
                (rationalp old) (rationalp new) (<= old new))
           (equal (fn-ccp-coverage-framed framed digest new frontier)
                  (fn-ccp-coverage-framed framed digest old frontier))))

(in-theory (disable fn-ccp-observe-framed fn-ccp-coverage-framed
                    fn-ccp-framed-boundary))
