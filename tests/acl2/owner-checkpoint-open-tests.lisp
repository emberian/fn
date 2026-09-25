; Teeth for books/owner-checkpoint-open.
;
; The witness is store-checkpoint-open-tests' image: two retention events
; and two configuration records, the second at txid 7 after both events,
; split after the first event.  The owner installed from the checkpoint is
; the owner the full open installs, and it is a configured owner, not :fault.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/owner-checkpoint-open")

(defconst *ock-t-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "forward-ock" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "forward-ock" "subject" "evidence" 0)))
(defconst *ock-t-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1))
                            *fn-cfg-default-stamp*)))
(defconst *ock-t-prefix* (list (car *ock-t-events*)))
(defconst *ock-t-suffix* (cdr *ock-t-events*))
(defconst *ock-t-full* (fn-ock-recover-full *ock-t-configs* 8 *ock-t-events* 4))
(defconst *ock-t-extended*
  (fn-sco-extend (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                 *ock-t-configs* *ock-t-suffix*))

; The keystone, evaluated on a reachable owner.
(assert-event (not (equal *ock-t-full* :fault)))
(assert-event (fn-ocl-relation *ock-t-full*))
(assert-event (equal (fn-ock-recover-extended *ock-t-extended* *ock-t-configs* 8 4)
                     *ock-t-full*))
; The full path: the empty capture extended over the whole history.
(assert-event (equal (fn-ock-recover-extended
                      (fn-sco-extend (fn-sco-capture *ock-t-configs* nil)
                                     *ock-t-configs* *ock-t-events*)
                      *ock-t-configs* 8 4)
                     *ock-t-full*))
; The extended value is the capture of the whole history: the owner's base.
(assert-event (equal *ock-t-extended*
                     (fn-sco-capture *ock-t-configs* *ock-t-events*)))
; The configuration the owner serves is the replay's last generation.
(assert-event (equal (fn-cfg-generation (fn-ocfg-config *ock-t-full*)) 2))

; The keystone is not vacuous: a checkpoint of a different prefix installs a
; different owner (the checkpoint's records are the Store's history).
(must-fail
 (defthm ock-t-other-prefix
   (equal (fn-ock-recover-extended
           (fn-sco-extend (fn-sco-capture *ock-t-configs* *ock-t-suffix*)
                          *ock-t-configs* *ock-t-suffix*)
           *ock-t-configs* 8 4)
          *ock-t-full*)))

; fn-ock-recover-installs-ocl-relation, its one hypothesis (the host did not
; refuse): a refused install (connection bound not natural) is :fault, and
; :fault satisfies no relation.
(assert-event (equal (fn-ock-recover-extended *ock-t-extended* *ock-t-configs* 8 nil)
                     :fault))
(must-fail
 (defthm ock-t-relation-without-install
   (fn-ocl-relation (fn-ock-recover-extended *ock-t-extended* *ock-t-configs* 8 nil))))

; The publication keystone.  Witness: from the capture of the prefix the
; owner publishes the capture of the whole history, by extension.
(assert-event (fn-sn-observed-historyp 8 *ock-t-events*))
(assert-event (equal (fn-ock-next-checkpoint
                      (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                      *ock-t-configs* *ock-t-events*)
                     (fn-sco-capture *ock-t-configs* *ock-t-events*)))
(assert-event (equal (fn-sco-open (fn-ock-next-checkpoint
                                   (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                                   *ock-t-configs* *ock-t-events*)
                                  *ock-t-configs* 8 nil)
                     (fn-cpo-open-observed *ock-t-configs* 8 *ock-t-events*)))
; Its hypothesis (an admitted history) has NO must-fail: the identity
; fold's append lemma takes it, but the fault that fold stops on is
; absorbing, and these non-admitted histories give the capture too.  The
; hypothesis is therefore reported untoothed (planning/evidence/
; owner-checkpoint-open-2026-09-25.md); the owner's history always meets it.
(defconst *ock-t-improper* (cons (car *ock-t-events*) 'tail))
(assert-event (not (fn-sn-observed-historyp 8 *ock-t-improper*)))
(assert-event (not (fn-sn-observed-historyp 8 (list 'junk 'junk2))))
(assert-event (equal (fn-ock-next-checkpoint (fn-sco-capture *ock-t-configs* (list 'junk))
                                             *ock-t-configs* (list 'junk 'junk2))
                     (fn-sco-capture *ock-t-configs* (list 'junk 'junk2))))
(assert-event (equal (fn-ock-next-checkpoint (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                                             *ock-t-configs* *ock-t-improper*)
                     (fn-sco-capture *ock-t-configs* *ock-t-improper*)))

; The publication policy: not due below K/2, due at K/2, and not again at the
; count of a failed attempt.
(assert-event (not (fn-ock-publication-duep 0 1 4 nil)))
(assert-event (fn-ock-publication-duep 0 2 4 nil))
(assert-event (fn-ock-publication-duep nil 2 4 nil))
(assert-event (not (fn-ock-publication-duep 0 2 4 2)))
(assert-event (fn-ock-publication-duep 0 3 4 2))
(assert-event (equal (car (fn-sco-select :ok 0 1 4)) :checkpoint))
; fn-ock-not-due-keeps-the-checkpoint-open, one must-fail per hypothesis.
(must-fail
 (defthm ock-t-not-due-without-natp-durable
   (equal (car (fn-sco-select :ok nil 0 5)) :checkpoint)))
(assert-event (not (fn-ock-publication-duep nil 0 5 nil)))
(must-fail
 (defthm ock-t-not-due-without-natp-count
   (equal (car (fn-sco-select :ok 0 nil 5)) :checkpoint)))
(assert-event (not (fn-ock-publication-duep 0 nil 5 nil)))
(must-fail
 (defthm ock-t-not-due-without-durable-below-count
   (equal (car (fn-sco-select :ok 5 3 5)) :checkpoint)))
(assert-event (not (fn-ock-publication-duep 5 3 5 nil)))
(must-fail
 (defthm ock-t-not-due-without-natp-k
   (equal (car (fn-sco-select :ok 0 0 nil)) :checkpoint)))
(assert-event (not (fn-ock-publication-duep 0 0 nil 1)))
(must-fail
 (defthm ock-t-not-due-without-a-new-count
   (equal (car (fn-sco-select :ok 0 20 4)) :checkpoint)))
(assert-event (not (fn-ock-publication-duep 0 20 4 20)))

; -----------------------------------------------------------------------------
; checkpoint-cost (PKT-141)

; The file carries the count.  Witness: the capture of the whole history
; freezes to its count, and thaws back to itself.
(defconst *ock-t-capture* (fn-sco-capture *ock-t-configs* *ock-t-events*))
(assert-event (equal (fn-sco-at 1 (fn-sco-freeze *ock-t-capture*)) 2))
(assert-event (equal (fn-sco-thaw (fn-sco-freeze *ock-t-capture*)) *ock-t-capture*))
; The count form is not the list form: the file differs.
(assert-event (not (equal (fn-sco-freeze *ock-t-capture*) *ock-t-capture*)))
; fn-sco-thaw-of-freeze, its one hypothesis (a checkpoint's shape): a value
; whose record slot is already a count is not one, and it does not come back.
(defconst *ock-t-not-shape* (list :fn-store-checkpoint 2 nil nil nil nil nil))
(assert-event (not (equal (fn-sco-thaw (fn-sco-freeze *ock-t-not-shape*))
                          *ock-t-not-shape*)))
; (Stated at the concrete value, so ACL2 refutes it by evaluation instead of
; searching.)
(must-fail
 (defthm ock-t-thaw-without-shape
   (implies (equal c *ock-t-not-shape*)
            (equal (fn-sco-thaw (fn-sco-freeze c)) c))))
; A checkpoint whose index does not hold its records keeps the list.
(defconst *ock-t-unindexed*
  (fn-sco-make *ock-t-events* (fn-sco-cpr *ock-t-capture*)
               (fn-sco-identity *ock-t-capture*) (fn-sco-consumer *ock-t-capture*)
               (fn-sco-topic *ock-t-capture*) nil))
(assert-event (equal (fn-sco-freeze *ock-t-unindexed*) *ock-t-unindexed*))
(assert-event (equal (fn-sco-thaw (fn-sco-freeze *ock-t-unindexed*)) *ock-t-unindexed*))

; The codec round trip through the frozen file, on the witness.
; (Attachments evaluate in assert-event, not in defconst: the digest is
; fn-sha256's.)
(assert-event (let ((segments (fn-scc-segments (fn-sco-freeze *ock-t-capture*) 64)))
                (and (< 1 (len segments))
                     (equal (fn-sco-thaw (cadr (fn-scc-decode-segments segments)))
                            *ock-t-capture*))))
; Its tree hypothesis: a value the codec cannot encode does not come back.
(defconst *ock-t-untree*
  (fn-sco-make *ock-t-events* 1/2 nil nil nil nil))
(assert-event (not (fn-scc-treep (fn-sco-freeze *ock-t-untree*))))
(assert-event (equal (fn-scc-segments (fn-sco-freeze *ock-t-untree*) 64) :unencodable))
(must-fail
 (defthm ock-t-decode-without-tree
   (implies (and (equal c *ock-t-untree*)
                 (fn-sco-shapep c)
                 (< (+ 1 (len (fn-scc-encode (fn-sco-freeze c)))) *fn-scc-u64-bound*)
                 (< (fn-scc-value-sequence (fn-sco-freeze c)) *fn-scc-u64-bound*))
            (equal (fn-sco-thaw (cadr (fn-scc-decode-segments
                                       (fn-scc-segments (fn-sco-freeze c) 64))))
                   c))))
; The header carries S for the count form.
(assert-event (equal (fn-scc-value-sequence (fn-sco-freeze *ock-t-capture*)) 2))

; The one-pass Store open.  Witness: from the prefix's capture extended over
; the suffix, the open is the full open, :ok, and the configuration fold is
; the full replay.
(defconst *ock-t-store-open* (fn-sco-store-open *ock-t-extended* *ock-t-configs* 8))
(assert-event (equal (cadr *ock-t-store-open*)
                     (fn-cpo-open-observed *ock-t-configs* 8 *ock-t-events*)))
(assert-event (equal (fn-sn-open-kind (cadr *ock-t-store-open*)) :ok))
(assert-event (equal (car *ock-t-store-open*)
                     (fn-cpr-replay *ock-t-configs* *ock-t-events*)))
(assert-event (fn-sn-open-okp (cadr *ock-t-store-open*)))
; The owner from that pair is the full open's owner.
(assert-event (equal (fn-ock-install (car *ock-t-store-open*) (cadr *ock-t-store-open*) 4)
                     *ock-t-full*))

; The publication off the mutex.  Witness: from the prefix's capture over the
; captured history, NEXT is the capture of that history and the octets are its
; frozen file.
(assert-event (equal (car (fn-ock-publication (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                                               *ock-t-configs* *ock-t-events* 64))
                     *ock-t-capture*))
(assert-event (equal (cadr (fn-ock-publication (fn-sco-capture *ock-t-configs* *ock-t-prefix*)
                                                *ock-t-configs* *ock-t-events* 64))
                     (fn-scc-file-octets (fn-sco-freeze *ock-t-capture*) 64)))
; A later commit does not reach a publication already captured: capturing at
; the prefix publishes the prefix.
(assert-event (equal (car (fn-ock-publication
                           (fn-sco-capture *ock-t-configs* nil)
                           *ock-t-configs* *ock-t-prefix* 64))
                     (fn-sco-capture *ock-t-configs* *ock-t-prefix*)))
; fn-sco-store-open-of-extended-capture, the hypothesis of its second
; conjunct (the open is :ok) has NO must-fail: on these refused opens (a
; repeated history, an improper prefix, a non-event prefix) the configuration
; fold still equals the full replay.  It is reported untoothed; the host
; reads the configuration only after testing the kind
; (fn-store-sn-open-extended, host/store-node-host.lisp).
(assert-event
 (let ((r (fn-sco-store-open (fn-sco-extend (fn-sco-capture *ock-t-configs* *ock-t-events*)
                                            *ock-t-configs* *ock-t-events*)
                             *ock-t-configs* 8)))
   (and (equal (fn-sn-open-kind (cadr r)) :error)
        (equal (car r) (fn-cpr-replay *ock-t-configs*
                                      (append *ock-t-events* *ock-t-events*))))))
(assert-event
 (let ((r (fn-sco-store-open (fn-sco-extend (fn-sco-capture *ock-t-configs* (list 5))
                                            *ock-t-configs* *ock-t-suffix*)
                             *ock-t-configs* 8)))
   (and (equal (fn-sn-open-kind (cadr r)) :error)
        (equal (car r) (fn-cpr-replay *ock-t-configs* (cons 5 *ock-t-suffix*))))))
