; Teeth for books/record-width-producers (PRF-123): reachable witnesses, one
; counterexample per hypothesis, and the boundary vectors 2^32 - 1, 2^32,
; 2^64 - 1 and 2^64 at the producer's inputs.
(in-package "ACL2")
(include-book "store-node-tests")
(include-book "../../books/record-width-producers")
(include-book "std/testing/must-fail" :dir :system)

(defconst *rwpt-obs* (fn-clock-observation 1 841000000000 0 t))
(defun rwpt-article (s charge)
  (fn-sn-article-record s *rwpt-obs* "<sn@example>" '(65 66) *sn-groups*
                        "sn-pin" "sn-content" "sn-release" charge))

; ---------------------------------------------------------------------------
; KEYSTONE fn-sn-prepare-stages-a-narrow-article-record.
; Reachable positive witness: the reserved store stages the article the
; producer builds, at charge 2, and it is narrow with sequence, txid and
; generation 0 (the allocator's first reservation).
(assert-event
 (let ((r (rwpt-article *sn-reserved* 2)))
   (and (fn-sn-statep *sn-reserved*)
        (fn-record-uint32p 2)
        (not (equal (fn-sn-prepare *sn-reserved* r) *sn-reserved*))
        (not (fn-record-widep r))
        (equal (fn-record-sequence r) 0)
        (equal (fn-record-txid r) 0)
        (equal (fn-record-generation r) 0)
        (equal (fn-record-stamp r) 841000000))))
; Boundary vectors at the charge the producer carries, in a reserved store
; whose retention capacity (an operator setting, any natural) is 2^65: 2^32 -
; 1 is staged narrow; 2^32 and 2^64 - 1 are staged and wide (schema 2), which
; is the counterexample for the charge hypothesis: the prepare does not
; refuse a wide charge, so the hypothesis is what bounds it; 2^64 is not a
; record (`fn-record-p' is u64) and the prepare refuses it.  (At the fixture's
; capacity 10 the retention gate refuses every charge above 10.)
(defconst *rwpt-big* (fn-sn-test-reserve (fn-sn-initial *sn-groups* (expt 2 65))))
(assert-event
 (let ((r (rwpt-article *rwpt-big* 4294967295)))
   (and (not (equal (fn-sn-prepare *rwpt-big* r) *rwpt-big*))
        (not (fn-record-widep r))
        (equal (fn-record-schema-octet r) 1))))
(assert-event
 (let ((r (rwpt-article *rwpt-big* 4294967296)))
   (and (not (equal (fn-sn-prepare *rwpt-big* r) *rwpt-big*))
        (not (fn-record-uint32p 4294967296))
        (fn-record-widep r)
        (equal (fn-record-schema-octet r) 2))))
(assert-event
 (let ((r (rwpt-article *rwpt-big* 18446744073709551615)))
   (and (not (equal (fn-sn-prepare *rwpt-big* r) *rwpt-big*))
        (fn-record-widep r))))
(assert-event
 (let ((r (rwpt-article *rwpt-big* 18446744073709551616)))
   (and (not (fn-record-p r))
        (equal (fn-sn-prepare *rwpt-big* r) *rwpt-big*))))
(must-fail
 (defthm rwpt-narrow-without-the-charge-hypothesis
   (implies (not (equal (fn-sn-prepare
                         s (fn-sn-article-record s obs msgid payload groups
                                                 obligation-id subject
                                                 evidence charge))
                        s))
            (not (fn-record-widep
                  (fn-sn-article-record s obs msgid payload groups
                                        obligation-id subject evidence
                                        charge))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-sn-prepare-stages-u32-coordinates
                                    (record (fn-sn-article-record
                                             s obs msgid payload groups
                                             obligation-id subject evidence
                                             charge))))))))
; Corrupted-state witness for the prepare hypothesis (not reachable: the
; allocator never counts 2^32 records): the reserved store with its identity
; counter set to 2^32.  The producer builds a wide record (sequence 2^32) at
; charge 2, and the prepare refuses it (sequence is not the committed
; count), so without the hypothesis the conclusion fails.
(defconst *rwpt-corrupt* (update-nth 9 4294967296 *sn-reserved*))
(assert-event (equal (fn-sn-identity-next *rwpt-corrupt*) 4294967296))
(assert-event
 (let ((r (rwpt-article *rwpt-corrupt* 2)))
   (and (fn-record-uint32p 2)
        (fn-record-p r)
        (fn-record-widep r)
        (equal (fn-record-sequence r) 4294967296)
        (equal (fn-sn-prepare *rwpt-corrupt* r) *rwpt-corrupt*))))
(must-fail
 (defthm rwpt-narrow-without-the-prepare-hypothesis
   (implies (fn-record-uint32p charge)
            (not (fn-record-widep
                  (fn-sn-article-record s obs msgid payload groups
                                        obligation-id subject evidence
                                        charge))))
   :rule-classes nil))

; ---------------------------------------------------------------------------
; The allocator lemma at the file machine: the frontier is u32 in every
; file state, and 2^32 is not.
(assert-event (fn-sf-statep (fn-sn-files *sn-reserved*)))
(assert-event (equal (fn-sf-frontier (fn-sn-files *sn-reserved*)) 1))
(assert-event (not (fn-sf-statep (update-nth 2 4294967296
                                             (fn-sn-files *sn-reserved*)))))

; ---------------------------------------------------------------------------
; The charge gate: 2^32 - 1 is admitted, 2^32 is refused by name.
(defconst *rwpt-scale* (fn-bs-config-for-profile :scale))
(defconst *rwpt-msgid-octets*
  '(60 115 110 64 101 120 97 109 112 108 101 62))
(assert-event (equal (fn-sbud-post-boundary *rwpt-scale* *rwpt-msgid-octets*
                                            2 2 4294967295)
                     :ok))
(assert-event (equal (fn-sbud-post-boundary *rwpt-scale* *rwpt-msgid-octets*
                                            2 2 4294967296)
                     :charge-bound))

; ---------------------------------------------------------------------------
; fn-post-admitted-article-record-is-within-r, at the saved scale profile.
(assert-event
 (let ((r (rwpt-article *sn-reserved* 2)))
   (and (fn-bs-profile-admittedp *rwpt-scale*)
        (equal (fn-sbud-post-boundary *rwpt-scale* *rwpt-msgid-octets*
                                      (len '(65 66)) (len *sn-groups*) 2)
               :ok)
        (not (equal (fn-sn-prepare *sn-reserved* r) *sn-reserved*))
        (equal (fn-bs-profile-max-record-octets *rwpt-scale*) 17138486)
        (<= (len (fn-record-encode r)) 17138486))))
; The boundary hypothesis: under a value that is not a profile the boundary
; refuses (:payload-bound), R reads 0, and the staged record encodes past it.
(assert-event
 (let ((r (rwpt-article *sn-reserved* 2)))
   (and (not (equal (fn-sbud-post-boundary '(1 2 3) *rwpt-msgid-octets*
                                            2 2 2)
                    :ok))
        (not (equal (fn-sn-prepare *sn-reserved* r) *sn-reserved*))
        (< (fn-bs-profile-max-record-octets '(1 2 3))
           (len (fn-record-encode r))))))

; ---------------------------------------------------------------------------
; fn-bpi-staged-record-is-narrow: the BP ingress producer.  The fixture is
; tests/acl2/bp-ingress-tests' (policy charge 3); the witness is the record
; `fn-bpi-ingress-prepare' stages, rebuilt through `fn-bpi-record-for'.
(defconst *rwpt-bpi-map*
  (list (list '(102 110 46 108 101 116 116 101 114 115) "fn.letters")
        (list '(102 110 46 116 101 115 116) "fn.test")))
(defun rwpt-bpi-policy (charge)
  (fn-bpi-make-policy "dtn://fn.example/inbox" "dtn://fn.example/inbox"
                      *rwpt-bpi-map* "archive:bp-1" "legacy-article:bp-1"
                      "unsigned-ingress-v0" charge "bp-policy-v0" "bp-terms-v0"
                      "dtn://fn.example"))
(defconst *rwpt-bpi-context*
  (fn-bpi-make-context "dtn://fn.example/inbox" "dtn://peer.example"
                       "bpa-local-42" 3600 (fn-clock-observation 1 841000000000 0 t)))
(defconst *rwpt-bpi-msgid* '(60 98 112 45 49 64 101 120 97 109 112 108 101 62))
(defconst *rwpt-bpi-groups* '((102 110 46 108 101 116 116 101 114 115)))
(defconst *rwpt-bpi-adu* '(66 111 100 121 13 10))
(defun rwpt-bpi-record (store charge)
  (fn-bpi-record-for store (rwpt-bpi-policy charge) *rwpt-bpi-context*
                     *rwpt-bpi-msgid* *rwpt-bpi-groups* *rwpt-bpi-adu*))
(defconst *rwpt-bpi-store*
  (fn-sn-test-reserve (fn-sn-initial *sn-groups* (expt 2 65))))
(assert-event
 (let ((r (rwpt-bpi-record *rwpt-bpi-store* 3)))
   (and (fn-bpi-policy-p (rwpt-bpi-policy 3))
        (not (equal (fn-sn-prepare *rwpt-bpi-store* r) *rwpt-bpi-store*))
        (not (fn-record-widep r))
        (equal (fn-record-charge r) 3))))
; The policy hypothesis: a policy charging 2^32 is not `fn-bpi-policy-p',
; and the record built under it is staged and wide.
(assert-event
 (let ((r (rwpt-bpi-record *rwpt-bpi-store* 4294967296)))
   (and (not (fn-bpi-policy-p (rwpt-bpi-policy 4294967296)))
        (not (equal (fn-sn-prepare *rwpt-bpi-store* r) *rwpt-bpi-store*))
        (fn-record-widep r))))
; The prepare hypothesis: the corrupted store (identity counter 2^32) builds
; a wide record under the admitted policy and the prepare refuses it.
(defconst *rwpt-bpi-corrupt* (update-nth 9 4294967296 *rwpt-bpi-store*))
(assert-event
 (let ((r (rwpt-bpi-record *rwpt-bpi-corrupt* 3)))
   (and (fn-bpi-policy-p (rwpt-bpi-policy 3))
        (equal (fn-sn-prepare *rwpt-bpi-corrupt* r) *rwpt-bpi-corrupt*)
        (fn-record-widep r))))

; ===========================================================================
; PRF-126: the producer ceiling.
; KEYSTONE fn-record-encode-producer-length-bound (records-seam), a
; non-degenerate witness at the tightest shape: sequence, txid, generation
; and stamp at 2^32 (eight-octet heads, schema 2), charge 2^32 - 1, a
; 250-octet Message-ID, three 256-octet metadata strings, a 65 536-octet
; payload (a five-octet head) and no group: 66 618 octets against the
; ceiling 66 619.  With one 256-octet group, 66 877 against 66 880 -- the
; record the bounds-p6 record found one octet past R = 66 880 with all FIVE
; fields wide.
(defconst *rwpt-meta* (coerce (make-list 256 :initial-element #\m) 'string))
(defconst *rwpt-msgid250* (coerce (make-list 250 :initial-element #\a) 'string))
(defconst *rwpt-group256* (coerce (make-list 256 :initial-element #\g) 'string))
(defconst *rwpt-payload* (make-list 65536 :initial-element 65))
(defun rwpt-wide (groups charge)
  (fn-record-make 4294967296 4294967296 4294967296 *rwpt-msgid250*
                  *rwpt-payload* groups *rwpt-meta* *rwpt-meta* *rwpt-meta*
                  charge 4294967296))
(assert-event
 (let ((r (rwpt-wide nil 4294967295)))
   (and (fn-record-p r)
        (fn-record-uint32p (fn-record-charge r))
        (fn-record-widep r)
        (equal (fn-record-schema-octet r) 2)
        (equal (len (fn-record-encode r)) 66618)
        (equal (fn-record-encoded-octets-ceiling 65536 0) 66619))))
(assert-event
 (let ((r (rwpt-wide (list *rwpt-group256*) 4294967295)))
   (and (fn-record-p r)
        (fn-record-widep r)
        (equal (len (fn-record-encode r)) 66877)
        (equal (fn-record-encoded-octets-ceiling 65536 1) 66880))))
; Its hypothesis: the same records with charge 2^32 (a ninth-octet head)
; encode 66 622 > 66 619 and 66 881 > 66 880.
(assert-event
 (let ((r (rwpt-wide nil 4294967296)))
   (and (fn-record-p r)
        (not (fn-record-uint32p (fn-record-charge r)))
        (< (fn-record-encoded-octets-ceiling 65536 0) (len (fn-record-encode r))))))
(assert-event
 (let ((r (rwpt-wide (list *rwpt-group256*) 4294967296)))
   (and (fn-record-p r)
        (equal (len (fn-record-encode r)) 66881))))
(must-fail
 (defthm rwpt-producer-ceiling-without-the-charge-hypothesis
   (<= (len (fn-record-encode record))
       (fn-record-encoded-octets-ceiling (len (fn-record-payload record))
                                         (len (fn-record-groups record))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-record-encode-producer-length-bound))))))

; fn-sn-prepare-stages-an-article-record-within-its-ceiling: the reachable
; witness is the fixture store's record at charge 2; the charge hypothesis's
; counterexample is the staged record at charge 2^64 - 1 in the 2^65-capacity
; store, which the prepare stages and which is still within the ceiling at
; this small shape, so the tooth is the seam theorem's above (the prepare
; does not bound the charge; the hypothesis is what does).
(assert-event
 (let ((r (rwpt-article *sn-reserved* 2)))
   (and (fn-record-uint32p 2)
        (not (equal (fn-sn-prepare *sn-reserved* r) *sn-reserved*))
        (<= (len (fn-record-encode r))
            (fn-record-encoded-octets-ceiling 2 (len *sn-groups*))))))
(assert-event
 (let ((r (rwpt-article *rwpt-big* 18446744073709551615)))
   (and (not (fn-record-uint32p 18446744073709551615))
        (not (equal (fn-sn-prepare *rwpt-big* r) *rwpt-big*)))))
(must-fail
 (defthm rwpt-within-ceiling-without-the-prepare-hypothesis
   (implies (fn-record-uint32p charge)
            (<= (len (fn-record-encode
                      (fn-sn-article-record s obs msgid payload groups
                                            obligation-id subject evidence
                                            charge)))
                (fn-record-encoded-octets-ceiling (len payload) (len groups))))
   :rule-classes nil))

; fn-bs-profile-admits-every-producer-record at the saved scale profile: the
; wide G = 1 record above is within A and G and encodes within R.
(assert-event
 (let ((r (rwpt-wide (list *rwpt-group256*) 4294967295)))
   (and (fn-bs-profile-admittedp *rwpt-scale*)
        (<= 65536 (fn-bs-profile-max-article-octets *rwpt-scale*))
        (<= 1 (fn-bs-profile-max-groups-per-article *rwpt-scale*))
        (<= (len (fn-record-encode r))
            (fn-bs-profile-max-record-octets *rwpt-scale*)))))

; fn-bpi-staged-record-fits-the-producer-ceiling: the BP fixture record at
; policy charge 3 is staged and within its ceiling; the policy hypothesis's
; tooth is the seam theorem's (a policy charge above u32 is not a policy).
(assert-event
 (let ((r (rwpt-bpi-record *rwpt-bpi-store* 3)))
   (and (fn-bpi-policy-p (rwpt-bpi-policy 3))
        (not (equal (fn-sn-prepare *rwpt-bpi-store* r) *rwpt-bpi-store*))
        (<= (len (fn-record-encode r))
            (fn-record-encoded-octets-ceiling (len (fn-record-payload r))
                                              (len (fn-record-groups r)))))))
