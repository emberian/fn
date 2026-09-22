; Witnesses and teeth for books/checkpoint-codec.lisp.
;
; The witness is the reachable checkpoint of tests/acl2/checkpoint-tests:
; one committed record, a consumed allocator frontier ahead of it (known
; aborts), captured by the production fn-checkpoint-capture.  Every keystone
; is exercised on it, and each hypothesis has a case in which dropping it
; makes the conclusion fail on an executable counterexample.
(in-package "ACL2")
(include-book "../../books/checkpoint-codec")

(defconst *cpc-groups* '("fn.letters" "fn.test"))
(defconst *cpc-r0*
  (fn-record-make 0 0 0 "<cp0@example.invalid>" '(65 13 10)
                  '("fn.letters") "cp-pin-0" "cp-content-0" "cp-release-0" 2))
(defconst *cpc-r1*
  (fn-record-make 1 4 4 "<cp1@example.invalid>" '(66 13 10)
                  '("fn.test") "cp-pin-1" "cp-content-1" "cp-release-1" 3))
(defconst *cpc-prefix* (list *cpc-r0*))
(defconst *cpc-capture* (fn-checkpoint-capture *cpc-groups* 10 *cpc-prefix* 3))
(defconst *cpc-value* (fn-checkpoint-capture-value *cpc-capture*))
(assert-event (equal (car *cpc-capture*) :ok))
(assert-event (fn-checkpointp *cpc-value*))

; -----------------------------------------------------------------------------
; The whole node is in the value universe and the checkpoint encodes.

(assert-event (fn-cpc-treep (fn-checkpoint-node *cpc-value*)))
(assert-event (fn-cpc-encodablep *cpc-value*))
(defconst *cpc-octets* (fn-cpc-encode *cpc-value*))
(assert-event (and (consp *cpc-octets*) (fn-cbor-octet-listp *cpc-octets*)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-cpc-decode-of-encode: value direction, at the capture's own
; bounds and at later (larger) observed bounds.

(assert-event (equal (fn-cpc-decode *cpc-octets* *cpc-groups* 10 3 1)
                     (list :ok *cpc-value*)))
(assert-event (equal (fn-cpc-decode *cpc-octets* *cpc-groups* 10 40 9)
                     (list :ok *cpc-value*)))

; Teeth: each hypothesis.  Frontier bound dropped (observed frontier behind
; the checkpoint's): refused as :frontier, not :ok.
(assert-event (not (equal (fn-cpc-decode *cpc-octets* *cpc-groups* 10 2 1)
                             (list :ok *cpc-value*))))
(assert-event (equal (fn-cpc-decode *cpc-octets* *cpc-groups* 10 2 1)
                     '(:error :frontier)))
; Count bound dropped: refused as :sequence.
(assert-event (not (equal (fn-cpc-decode *cpc-octets* *cpc-groups* 10 3 0)
                             (list :ok *cpc-value*))))
(assert-event (equal (fn-cpc-decode *cpc-octets* *cpc-groups* 10 3 0)
                     '(:error :sequence)))
; Encodability dropped: a checkpoint whose node holds a symbol outside the
; table has no encoding, so there is nothing to decode.
(defconst *cpc-alien*
  (fn-cpc-assemble *cpc-groups* 10 3 1 (list :not-a-node-symbol)))
(assert-event (not (fn-cpc-encodablep *cpc-alien*)))
(assert-event (null (fn-cpc-encode *cpc-alien*)))
(assert-event (not (equal (fn-cpc-decode (fn-cpc-encode *cpc-alien*)
                                            *cpc-groups* 10 3 1)
                             (list :ok *cpc-alien*))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-cpc-accepted-input-is-canonical: byte direction.

(assert-event
 (equal (fn-cpc-encode (fn-cpc-result-value
                        (fn-cpc-decode *cpc-octets* *cpc-groups* 10 3 1)))
        *cpc-octets*))

; Teeth: the theorem's only hypothesis is acceptance.  A refused input has
; no value to re-encode; the alternative (non-canonical) spellings below are
; exactly the inputs whose acceptance would break the theorem, and each is
; refused by the clause named.

; An octet list spelled as a cons chain (tag 4 1 1 4 1 2 0) instead of a
; bytes item (5 <bytes 1 2>): refused as :noncanonical.
(assert-event (equal (fn-cpc-decode-tree '(4 1 1 4 1 2 0) 7)
                     '(:error :noncanonical)))
(assert-event (equal (fn-cpc-decode-tree '(5 66 1 2) 4)
                     (fn-record-parse-ok '(1 2) nil)))
(assert-event (equal (fn-cpc-encode-tree '(1 2)) '(5 66 1 2)))
(assert-event (not (equal (fn-cpc-encode-tree
                              (fn-record-parse-value
                               (fn-cpc-decode-tree '(4 1 1 4 1 2 0) 7)))
                             '(4 1 1 4 1 2 0))))
; An empty bytes item under the octet-list tag would be a second spelling
; of nil: refused.
(assert-event (equal (fn-cpc-decode-tree '(5 64) 2) '(:error :noncanonical)))
(assert-event (equal (fn-cpc-decode-tree '(0) 1) (fn-record-parse-ok nil nil)))
; A non-minimal CBOR head (24 0 for the uint 0) is refused by the primitive.
(assert-event (equal (fn-cpc-decode-tree '(24 0) 2) '(:error :noncanonical)))
; Symbol codes outside the table.
(assert-event (equal (fn-cpc-decode-tree '(3 0) 2) '(:error :symbol)))
(assert-event (equal (fn-cpc-decode-tree '(3 4) 2) '(:error :symbol)))
(assert-event (equal (fn-cpc-decode-tree '(3 2) 2)
                     (fn-record-parse-ok :archive nil)))
(assert-event (equal (fn-cpc-decode-tree '(3 1) 2) (fn-record-parse-ok t nil)))
; Unknown tag and exhausted depth fuel.
(assert-event (equal (fn-cpc-decode-tree '(9) 1) '(:error :tag)))
(assert-event (equal (fn-cpc-decode-tree '(4 0 0) 1) '(:error :depth)))
(assert-event (equal (fn-cpc-decode-tree '(4 0 0) 2)
                     (fn-record-parse-ok '(nil) nil)))
; A cons whose car is not an octet is a cons however its cdr is spelled.
(assert-event (equal (fn-cpc-decode-tree '(4 2 65 97 5 66 1 2) 8)
                     (fn-record-parse-ok '("a" 1 2) nil)))
(assert-event (equal (fn-cpc-encode-tree '("a" 1 2)) '(4 2 65 97 5 66 1 2)))

; -----------------------------------------------------------------------------
; Hostile candidates: refused, and refused before the node item is parsed.

(defconst *cpc-header* (fn-cpc-encode-header 1 3 10 *cpc-groups*))
(assert-event (equal (append *cpc-header*
                             (fn-cpc-encode-tree (fn-checkpoint-node *cpc-value*)))
                     *cpc-octets*))

; The acceptance recogniser is anchored positively first, so the refusals
; below separate two answers instead of naming a constantly false predicate.
(assert-event (fn-cpc-result-okp (fn-cpc-decode *cpc-octets* *cpc-groups* 10 3 1)))
; Bad length: a truncated and an overlong payload.
(assert-event (not (fn-cpc-result-okp
                    (fn-cpc-decode (take (- (len *cpc-octets*) 1) *cpc-octets*)
                                   *cpc-groups* 10 3 1))))
(assert-event (equal (fn-cpc-decode (append *cpc-octets* '(0)) *cpc-groups* 10 3 1)
                     '(:error :trailing)))
; Corrupt: the node item's first tag replaced by an unknown tag.
(assert-event (equal (fn-cpc-decode (append *cpc-header* '(9)) *cpc-groups* 10 3 1)
                     '(:error :tag)))
; Corrupt magic and version.
(assert-event (equal (fn-cpc-decode (list* 68 102 110 45 100 (nthcdr 5 *cpc-octets*))
                                    *cpc-groups* 10 3 1)
                     '(:error :magic)))
; Mismatched configuration, frontier and count: the verdict is the header's
; and is the same whatever follows it (fn-cpc-decode-rejects-*-before-node);
; here the node item is garbage that would itself be refused.
(assert-event (equal (fn-cpc-decode (append *cpc-header* '(9)) *cpc-groups* 9 3 1)
                     '(:error :configuration)))
(assert-event (equal (fn-cpc-decode (append *cpc-header* '(9)) '("fn.letters") 10 3 1)
                     '(:error :configuration)))
(assert-event (equal (fn-cpc-decode (append *cpc-header* '(9)) *cpc-groups* 10 2 1)
                     '(:error :frontier)))
(assert-event (equal (fn-cpc-decode (append *cpc-header* '(9)) *cpc-groups* 10 3 0)
                     '(:error :sequence)))
; Teeth for the before-node theorems: with the header matching, the same
; garbage node is what gets refused, so the header verdicts above were not
; the node's.
(assert-event (not (equal (fn-cpc-decode (append *cpc-header* '(9))
                                            *cpc-groups* 10 3 1)
                             '(:error :configuration))))
; A well-formed node that is not a checkpoint for this header (the frontier
; is below the node's next transaction id) is refused as :invalid.
(assert-event
 (equal (fn-cpc-decode (append (fn-cpc-encode-header 1 0 10 *cpc-groups*)
                               (fn-cpc-encode-tree (fn-checkpoint-node *cpc-value*)))
                       *cpc-groups* 10 3 1)
        '(:error :invalid)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-cpc-valid-is-capture-value: exact binding.  Its one hypothesis
; is FN-CPC-VALIDP; the journal-interval condition it used to carry beside it
; is now a clause of that recognizer.

(assert-event (fn-cpc-validp *cpc-value* *cpc-groups* 10 *cpc-prefix*))
(assert-event (fn-sf-record-listp *cpc-prefix* 0 0 (fn-checkpoint-frontier *cpc-value*)))
(assert-event
 (equal (fn-checkpoint-capture-value
         (fn-checkpoint-capture *cpc-groups* 10 *cpc-prefix*
                                (fn-checkpoint-frontier *cpc-value*)))
        *cpc-value*))

; Teeth.  Node equality dropped: a checkpoint of a different reachable
; prefix (two records, frontier 6) is a checkpoint, but it is not the capture
; of *CPC-PREFIX* at its frontier.
(defconst *cpc-other*
  (fn-checkpoint-capture-value
   (fn-checkpoint-capture *cpc-groups* 10 (list *cpc-r0* *cpc-r1*) 6)))
(assert-event (fn-checkpointp *cpc-other*))
(assert-event (not (fn-cpc-validp *cpc-other* *cpc-groups* 10 *cpc-prefix*)))
(assert-event (not (equal (fn-checkpoint-capture-value
                 (fn-checkpoint-capture *cpc-groups* 10 *cpc-prefix*
                                        (fn-checkpoint-frontier *cpc-other*)))
                *cpc-other*)))
; Sequence equality dropped: same node, wrong stored sequence.
(defconst *cpc-wrong-sequence*
  (fn-cpc-assemble *cpc-groups* 10 3 7 (fn-checkpoint-node *cpc-value*)))
(assert-event (fn-checkpointp *cpc-wrong-sequence*))
(assert-event (not (fn-cpc-validp *cpc-wrong-sequence* *cpc-groups* 10 *cpc-prefix*)))
(assert-event (not (equal (fn-checkpoint-capture-value
                 (fn-checkpoint-capture *cpc-groups* 10 *cpc-prefix* 3))
                *cpc-wrong-sequence*)))
; Configuration binding dropped: validating against a different group list
; is refused by the recognizer's binding, and the capture under that list
; is a different checkpoint.
(assert-event (not (fn-cpc-validp *cpc-value* '("fn.letters") 10 *cpc-prefix*)))
(assert-event (not (equal (fn-checkpoint-capture-value
                 (fn-checkpoint-capture '("fn.letters") 10 *cpc-prefix* 3))
                *cpc-value*)))
; -----------------------------------------------------------------------------
; KEYSTONE fn-cpc-valid-refuses-generation-mismatch, and the tooth for the
; journal-interval clause of FN-CPC-VALIDP itself.
;
; *CPC-R0-BAD-GENERATION* is *CPC-R0* with the generation it consumed moved
; off its txid 0 to 1, so it is not a journal record and
; FN-CHECKPOINT-CAPTURE refuses the one-record prefix as :history.
(defconst *cpc-r0-bad-generation*
  (fn-record-make 0 0 1 "<cp0@example.invalid>" '(65 13 10)
                  '("fn.letters") "cp-pin-0" "cp-content-0" "cp-release-0" 2))
(defconst *cpc-bad-prefix* (list *cpc-r0-bad-generation*))
(assert-event (not (equal (fn-store-event-generation *cpc-r0-bad-generation*)
                          (fn-store-event-txid *cpc-r0-bad-generation*))))
(assert-event (not (fn-sf-record-listp *cpc-bad-prefix* 0 0 3)))
(assert-event (equal (fn-checkpoint-capture *cpc-groups* 10 *cpc-bad-prefix* 3)
                     '(:error :history)))
; Why the clause is the only thing that can refuse this prefix: FN-REPLAY
; carries a record's generation into the node transitions and never compares
; it with the txid, so replaying the corrupt prefix returns *exactly* the
; replay of *CPC-PREFIX*.  Before the clause was added, FN-CPC-VALIDP
; compared only these two results and answered T here.
(assert-event (equal (fn-replay *cpc-groups* 10 *cpc-bad-prefix*)
                     (fn-replay *cpc-groups* 10 *cpc-prefix*)))
; Witness: both hypotheses hold on this prefix and validation refuses it.
(assert-event (member-equal *cpc-r0-bad-generation* *cpc-bad-prefix*))
(assert-event (not (fn-cpc-validp *cpc-value* *cpc-groups* 10 *cpc-bad-prefix*)))
; Tooth, membership hypothesis dropped: the same mismatching record, not a
; member of the prefix offered, and validation accepts.
(assert-event (not (member-equal *cpc-r0-bad-generation* *cpc-prefix*)))
(assert-event (fn-cpc-validp *cpc-value* *cpc-groups* 10 *cpc-prefix*))
; Tooth, mismatch hypothesis dropped: a record that is a member of the
; prefix and whose generation is its txid, and validation accepts.
(assert-event (member-equal *cpc-r0* *cpc-prefix*))
(assert-event (equal (fn-store-event-generation *cpc-r0*)
                     (fn-store-event-txid *cpc-r0*)))
(assert-event (fn-cpc-validp *cpc-value* *cpc-groups* 10 *cpc-prefix*))
; Tooth for the clause inside FN-CPC-VALIDP: drop it from the definition and
; fn-cpc-valid-is-capture-value is false, because the capture of this prefix
; is the refusal (:error :history) and not the checkpoint offered.
(assert-event (not (equal (fn-checkpoint-capture-value
                           (fn-checkpoint-capture *cpc-groups* 10
                                                  *cpc-bad-prefix* 3))
                          *cpc-value*)))

; -----------------------------------------------------------------------------
; The frame: its own magic and kind table, both directions, hostile frames.

(defconst *cpc-digest* (make-list 32 :initial-element 0))
(defconst *cpc-frame* (fn-cpc-frame-encode *cpc-value* *cpc-digest*))
(assert-event (fn-cbor-octet-listp *cpc-frame*))
(assert-event (equal (take 4 *cpc-frame*) *fn-cpc-frame-magic*))
(assert-event (equal (fn-cpc-frame-decode *cpc-frame* *cpc-digest*
                                          *cpc-groups* 10 3 1)
                     (list :ok *cpc-value*)))
(assert-event
 (equal (fn-cpc-frame-encode
         (fn-cpc-result-value
          (fn-cpc-frame-decode *cpc-frame* *cpc-digest* *cpc-groups* 10 3 1))
         *cpc-digest*)
        *cpc-frame*))
; Bad length, cut frame, corrupt trailer (the host's digest disagrees), and a
; store frame offered as a checkpoint: each a distinct refusal.
(assert-event (equal (fn-cpc-frame-decode (append *cpc-frame* '(0)) *cpc-digest*
                                          *cpc-groups* 10 3 1)
                     '(:error :length)))
(assert-event (equal (fn-cpc-frame-decode (take (- (len *cpc-frame*) 1) *cpc-frame*)
                                          *cpc-digest* *cpc-groups* 10 3 1)
                     '(:error :truncated)))
(assert-event (equal (fn-cpc-frame-decode *cpc-frame* (cons 1 (cdr *cpc-digest*))
                                          *cpc-groups* 10 3 1)
                     '(:error :integrity)))
(assert-event (equal (fn-cpc-frame-decode
                      (fn-frame-store-encode (fn-record-encode *cpc-r0*) *cpc-digest*)
                      *cpc-digest* *cpc-groups* 10 3 1)
                     '(:error :magic)))
; The selection marker: its own kind under the same magic.
(assert-event (equal (fn-cpc-selection-decode
                      (fn-cpc-selection-encode 7 *cpc-digest*) *cpc-digest*)
                     '(:ok 7)))
(assert-event (equal (fn-cpc-selection-decode *cpc-frame* *cpc-digest*)
                     '(:error :magic)))
(assert-event (equal (fn-cpc-frame-decode (fn-cpc-selection-encode 7 *cpc-digest*)
                                          *cpc-digest* *cpc-groups* 10 3 1)
                     '(:error :magic)))
(assert-event (equal (fn-cpc-selection-decode
                      (fn-cpc-selection-encode 7 *cpc-digest*)
                      (cons 1 (cdr *cpc-digest*)))
                     '(:error :integrity)))
