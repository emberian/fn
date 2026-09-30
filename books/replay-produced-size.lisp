; Actual replay decision plus same-parser child carries. Funding is separate.
(in-package "ACL2")
(include-book "replay-identity-produced")
(include-book "identity-context-size")
(include-book "replay-identity-size")
(defun fn-rips-lengths-p (sizes)
 (declare (xargs :guard t))
 (and (consp sizes) (natp (car sizes)) (consp (cdr sizes))
      (natp (cadr sizes)) (consp (cddr sizes)) (natp (caddr sizes))
      (null (cdddr sizes))))
(defun fn-rips-string (n)
 (declare (xargs :guard (natp n)))
 (list (+ 2 (fn-scs-width n) n) nil nil))
(defthm fn-rips-string-carryp
 (implies (natp n) (fn-scs-carryp (fn-rips-string n)))
 :hints (("Goal" :in-theory (enable fn-rips-string fn-scs-carryp))))
(local (defthm fn-rips-octets-carryp
 (implies (natp n) (fn-scs-carryp (fn-scs-octets n)))
 :hints (("Goal" :in-theory (enable fn-scs-octets fn-scs-carryp)))))
(defun fn-rips-verdict-carry (child sizes)
 (declare (xargs :guard t :verify-guards nil))
 (if (not (fn-rips-lengths-p sizes)) nil
  (fn-scs-spine
   (list (fn-ics-scalar (fn-stxe-sequence child))
         (fn-ics-scalar (fn-stxe-txid child))
         (fn-ics-scalar (fn-stxe-generation child))
         (fn-rips-string (car sizes))
         (fn-ics-scalar (fn-stxe-token child))
         (fn-scs-octets (cadr sizes))
         (fn-ics-scalar (fn-stxe-keyring-generation child))
         (fn-scs-octets (caddr sizes))))))
(verify-guards fn-rips-verdict-carry
 :hints (("Goal" :in-theory (e/d (fn-rips-lengths-p fn-scs-carry-listp) (fn-rips-string)))))
(local (defthm fn-rips-spine-carryp
 (implies (fn-scs-carry-listp cs) (fn-scs-carryp (fn-scs-spine cs)))
 :hints (("Goal" :induct (fn-scs-spine cs)
          :in-theory (enable fn-scs-spine fn-scs-carry-listp)))))
(defthm fn-rips-verdict-carry-shape
 (implies (fn-rips-lengths-p sizes)
          (fn-scs-carryp (fn-rips-verdict-carry child sizes)))
 :hints (("Goal" :in-theory (e/d (fn-rips-verdict-carry fn-rips-lengths-p fn-scs-carry-listp) (fn-rips-string)))))
(defun fn-ris-produced-step-with-effects (ctx fields event snapshot-carry)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (checked effect child sizes)
  (fn-replay-identity-produced-effects ctx event)
  (let ((child-carry (cond ((equal effect :snapshot) snapshot-carry)
                           ((equal effect :verdict) (fn-rips-verdict-carry child sizes))
                           (t nil))))
   (if (or (not (fn-ics-carriesp fields))
           (and (not (equal effect :none)) (not (fn-scs-carryp child-carry))))
    (mv checked nil :unavailable effect child sizes)
    (mv checked
     (fn-ics-fields checked
      (if (equal effect :snapshot) (fn-scs-cons child-carry (fn-ics-field 2 fields))
       (fn-ics-field 2 fields))
      (if (equal effect :verdict) (fn-scs-cons child-carry (fn-ics-field 3 fields))
       (fn-ics-field 3 fields))) :carried effect child sizes)))))
; Existing result semantics preserved; actual core sharing consumes the six
; results above from that SAME decision, never a parallel replay invocation.
(defun fn-ris-produced-step (ctx fields event snapshot-carry)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (checked next-fields status effect child sizes)
  (fn-ris-produced-step-with-effects ctx fields event snapshot-carry)
  (declare (ignore effect child sizes))
  (mv checked next-fields status)))
(local (defthm fn-rips-list-field-carryp
 (implies (and (fn-scs-carry-listp fields) (natp n) (< n (len fields)))
          (fn-scs-carryp (fn-ics-field n fields)))
 :hints (("Goal" :induct (fn-ics-field n fields)
          :in-theory (enable fn-ics-field fn-scs-carry-listp)))))
(local (defthm fn-rips-field-carryp
 (implies (and (fn-ics-carriesp fields) (natp n) (< n 6))
          (fn-scs-carryp (fn-ics-field n fields)))
 :hints (("Goal" :in-theory (e/d (fn-ics-carriesp)
             (fn-scs-fixed-carriesp fn-ics-field fn-scs-carry-listp))))))
(verify-guards fn-ris-produced-step-with-effects
 :hints (("Goal" :in-theory
  (disable fn-replay-identity-produced-effects fn-rpe-produced-effects
           fn-rpe-produce fn-rpe-result fn-rpe-lengths
           fn-rpe-carried-bindsp fn-rpe-revoked-bindsp fn-rpe-stxa-bindsp
           fn-rpe-snapshot-bindsp fn-rpe-verdict-effect))))
(verify-guards fn-ris-produced-step
 :hints (("Goal" :in-theory
  (disable fn-replay-identity-produced-effects fn-rpe-produced-effects
           fn-rpe-produce fn-rpe-result fn-rpe-lengths
           fn-rpe-carried-bindsp fn-rpe-revoked-bindsp fn-rpe-stxa-bindsp
           fn-rpe-snapshot-bindsp fn-rpe-verdict-effect))))
(defthm fn-ris-produced-step-is-public-replay
 (equal (mv-nth 0 (fn-ris-produced-step ctx fields event snapshot-carry))
        (fn-replay-identity-step ctx event))
 :rule-classes nil
 :hints (("Goal"
 :use (fn-replay-identity-produced-has-original-context-and-effects
       fn-replay-identity-effects-context-is-replay-by-definition)
 :in-theory (e/d (fn-ris-produced-step fn-ris-produced-step-with-effects)
  (fn-replay-identity-produced-effects fn-replay-identity-effects
   fn-replay-identity-step fn-ics-carriesp fn-scs-carryp
   fn-rips-verdict-carry fn-ics-fields fn-scs-cons)))))


(local (defthm fn-rips-string-summary
 (implies (and (stringp x) (equal n (length x)))
          (equal (fn-rips-string n) (fn-scs-summary x)))
 :hints (("Goal" :use fn-scs-atom-establishes-summary
  :in-theory (e/d (fn-rips-string fn-scs-atom fn-scs-atom-size fn-scc-octetp)
                  (fn-scs-atom-size-is-encoded-length fn-scs-atom-establishes-summary fn-scs-width fn-scs-summary fn-scc-atom-octets))))))

(local (defthm fn-rips-cbor-octets-are-store-octets
 (equal (fn-cbor-octet-listp xs) (fn-scc-octet-listp xs))
 :hints (("Goal" :induct (len xs)
          :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp
                             fn-scc-octet-listp fn-scc-octetp)))))

(local (defthm fn-rips-consp-positive-len
 (implies (consp xs) (< 0 (len xs)))
 :rule-classes :linear
 :hints (("Goal" :expand ((len xs))))))

(defthm fn-rips-verdict-carry-is-exact
 (implies (and (fn-stxe-p child) (fn-rips-lengths-p sizes)
               (equal sizes (list (length (fn-stxe-msgid child))
                                  (len (fn-stxe-detail child))
                                  (len (fn-stxe-profile child)))))
          (equal (fn-rips-verdict-carry child sizes) (fn-scs-summary child)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-scs-spine-preserves-canonical-size (xs child) (cs (list (fn-ics-scalar (fn-stxe-sequence child))
 (fn-ics-scalar (fn-stxe-txid child)) (fn-ics-scalar (fn-stxe-generation child))
 (fn-rips-string (car sizes)) (fn-ics-scalar (fn-stxe-token child))
 (fn-scs-octets (cadr sizes)) (fn-ics-scalar (fn-stxe-keyring-generation child))
 (fn-scs-octets (caddr sizes))))))
  :in-theory (e/d (fn-rips-verdict-carry fn-rips-lengths-p fn-ics-scalar
                   fn-stxe-p fn-stxe-msgid fn-stxe-detail fn-stxe-profile
                   fn-stxe-sequence fn-stxe-txid fn-stxe-generation
                   fn-stxe-token fn-stxe-keyring-generation fn-stxe-shapep
                   fn-record-uint32p fn-record-msgidp fn-stxe-tokenp
                   fn-stxe-bounded-octetsp fn-scs-correspondsp)
                  (fn-scs-spine fn-scs-spine-preserves-canonical-size fn-scs-summary fn-rips-string fn-scs-cons fn-scs-atom
                   fn-scs-octets length)))))

(local (defthm fn-rips-sized-child-is-record
 (implies (fn-stmt-okp (mv-nth 0 (fn-stxs-decode octets)))
          (fn-stxe-p (fn-stmt-value (mv-nth 0 (fn-stxs-decode octets)))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-stxs-decode fn-stxe-of-items fn-stxe-items-p
                   fn-stxe-p fn-stmt-ok fn-stmt-error fn-stmt-okp fn-stmt-value
                   fn-stmt-uint-item-p fn-stmt-bytes-item-p fn-record-uint32p
                   fn-stxe-sequence fn-stxe-txid fn-stxe-generation fn-stxe-msgid
                   fn-stxe-token fn-stxe-detail fn-stxe-keyring-generation fn-stxe-profile
                   fn-cbor-ag-cdr)
                  (fn-stmt-decode-items-sized-bounded-impl
                   fn-stmt-decode-items-bounded-impl fn-stmt-decode-items-prechecked
                   fn-stxe-make fn-stxe-tokenp fn-stxe-code-token fn-stxe-bounded-octetsp
                   fn-record-msgidp fn-record-octets-string
                   fn-rips-cbor-octets-are-store-octets))))))

(defthm fn-rips-produced-verdict-has-actual-lengths
 (implies (equal (mv-nth 1 (fn-replay-identity-produced-effects ctx event)) :verdict)
  (let ((child (mv-nth 2 (fn-replay-identity-produced-effects ctx event)))
        (sizes (mv-nth 3 (fn-replay-identity-produced-effects ctx event))))
   (and (fn-stxe-p child)
        (equal sizes (list (length (fn-stxe-msgid child))
                           (len (fn-stxe-detail child))
                           (len (fn-stxe-profile child)))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-rips-sized-child-is-record
          (octets (fn-stxa-verdict-event (fn-replay-identity-wire event))))
        (:instance fn-rpe-binding-consumers-require-parser-success
          (evidence (fn-rpe-produce (fn-replay-identity-wire event)))
          (snapshot (fn-stxk-find
           (fn-stxa-keyring-generation (fn-replay-identity-wire event))
           (fn-stxk-context-snapshots ctx))))
        (:instance fn-rpe-producer-retains-exact-event-and-parser-values
          (event (fn-replay-identity-wire event)))
        fn-rpe-produced-verdict-lengths-are-actual)
  :in-theory (e/d (fn-replay-identity-produced-effects
                   fn-rpe-produced-effects fn-rpe-verdict-effect)
                 (fn-replay-identity-wire fn-rpe-produce fn-rpe-result fn-rpe-lengths
                  fn-rpe-carried-bindsp fn-rpe-revoked-bindsp fn-rpe-stxa-bindsp
                  fn-rpe-snapshot-bindsp fn-stxs-decode fn-stmt-okp fn-stmt-value
                  fn-stxk-p fn-stxe-p fn-stxa-p fn-stxk-apply-snapshot
                  fn-stxk-apply-verdict fn-stxk-find fn-replay-apply-carried-verdict
                  fn-replay-apply-revoked-verdict fn-stxe-msgid fn-stxe-detail
                  fn-stxe-profile length len)))))

(local (defthm fn-rips-record-lengths-shape
 (implies (fn-stxe-p child)
  (fn-rips-lengths-p (list (length (fn-stxe-msgid child))
                          (len (fn-stxe-detail child)) (len (fn-stxe-profile child)))))
 :hints (("Goal" :in-theory (e/d (fn-rips-lengths-p fn-stxe-p fn-record-msgidp)
                     (fn-record-ascii-stringp fn-record-string-octets
                      fn-stxe-bounded-octetsp fn-stxe-tokenp fn-record-uint32p))))))

(defthm fn-rips-produced-verdict-carry-is-exact
 (implies (equal (mv-nth 1 (fn-replay-identity-produced-effects ctx event)) :verdict)
  (equal (fn-rips-verdict-carry
           (mv-nth 2 (fn-replay-identity-produced-effects ctx event))
           (mv-nth 3 (fn-replay-identity-produced-effects ctx event)))
         (fn-scs-summary (mv-nth 2 (fn-replay-identity-produced-effects ctx event)))))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-rips-produced-verdict-has-actual-lengths
        (:instance fn-rips-record-lengths-shape
           (child (mv-nth 2 (fn-replay-identity-produced-effects ctx event))))
        (:instance fn-rips-verdict-carry-is-exact
           (child (mv-nth 2 (fn-replay-identity-produced-effects ctx event)))
           (sizes (mv-nth 3 (fn-replay-identity-produced-effects ctx event)))))
  :in-theory (disable fn-replay-identity-produced-effects fn-rips-verdict-carry
                      fn-scs-summary fn-rips-lengths-p fn-stxe-p
                      fn-stxe-msgid fn-stxe-detail fn-stxe-profile))))

(local (defthm fn-rips-corresponding-carries-shape
 (implies (fn-scs-correspondsp fields ctx)
          (fn-scs-fixed-carriesp (len ctx) fields))
 :hints (("Goal" :induct (fn-scs-correspondsp fields ctx)
  :in-theory (enable fn-scs-correspondsp fn-scs-fixed-carriesp)))))

(local (defthm fn-rips-full-context-has-fixed-carries
 (implies (and (fn-ics-contextp ctx) (fn-scs-correspondsp fields ctx))
          (fn-ics-carriesp fields))
 :hints (("Goal" :use fn-rips-corresponding-carries-shape
  :in-theory (e/d (fn-ics-contextp fn-ics-carriesp)
                  (fn-scs-correspondsp fn-scs-fixed-carriesp))))))

(local (defthm fn-rips-produced-effect-is-tag
 (member-eq (mv-nth 1 (fn-replay-identity-produced-effects ctx event))
            '(:none :snapshot :verdict))
 :hints (("Goal" :in-theory (e/d (fn-replay-identity-produced-effects
                                  fn-replay-identity-produced-verdict-effect member-eq)
       (fn-replay-identity-wire fn-stxs-decode fn-stxe-decode-exact
        fn-stmt-okp fn-stmt-value fn-stxk-p fn-stxe-p fn-stxa-p
        fn-stxk-apply-snapshot fn-stxk-apply-verdict fn-stxk-find
        fn-stxa-bindsp fn-hsig-article-event-carried-bindsp
        fn-hsig-article-event-revoked-bindsp fn-hsig-article-event-snapshot-bindsp
        fn-replay-apply-carried-verdict fn-replay-apply-revoked-verdict))))))

(defthm fn-ris-produced-step-preserves-canonical-size
 (implies
  (and (fn-ics-contextp ctx) (fn-scs-correspondsp fields ctx)
       (implies (equal (mv-nth 1 (fn-replay-identity-produced-effects ctx event)) :snapshot)
                (equal snapshot-carry
                 (fn-scs-summary (mv-nth 2 (fn-replay-identity-produced-effects ctx event))))))
  (and (equal (mv-nth 2 (fn-ris-produced-step ctx fields event snapshot-carry)) :carried)
       (fn-scs-correspondsp
         (mv-nth 1 (fn-ris-produced-step ctx fields event snapshot-carry))
         (mv-nth 0 (fn-ris-produced-step ctx fields event snapshot-carry)))))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-rips-produced-effect-is-tag
        fn-replay-identity-produced-has-original-context-and-effects
        fn-rips-produced-verdict-carry-is-exact fn-rips-full-context-has-fixed-carries
        (:instance fn-ris-step-preserves-canonical-size (carries fields)
          (child-carry
           (cond ((equal (mv-nth 1 (fn-replay-identity-produced-effects ctx event)) :snapshot)
                  snapshot-carry)
                 ((equal (mv-nth 1 (fn-replay-identity-produced-effects ctx event)) :verdict)
                  (fn-rips-verdict-carry
                   (mv-nth 2 (fn-replay-identity-produced-effects ctx event))
                   (mv-nth 3 (fn-replay-identity-produced-effects ctx event))))
                 (t nil)))))
  :in-theory (e/d (fn-ris-produced-step fn-ris-step member-eq)
     (fn-rips-produced-effect-is-tag fn-ris-step-preserves-canonical-size
      fn-rips-full-context-has-fixed-carries
      fn-replay-identity-produced-effects fn-replay-identity-effects
      fn-ics-fields fn-ics-field fn-ics-carriesp fn-ics-contextp
      fn-rips-verdict-carry fn-scs-summary fn-scs-carryp fn-scs-cons
      fn-scs-correspondsp)))))
(defthm fn-ris-produced-packet-has-public-context-and-effects
 (and
  (equal (mv-nth 0 (fn-ris-produced-step-with-effects ctx fields event snapshot-carry))
         (fn-replay-identity-step ctx event))
  (equal (mv-nth 3 (fn-ris-produced-step-with-effects ctx fields event snapshot-carry))
         (mv-nth 1 (fn-replay-identity-effects ctx event)))
  (equal (mv-nth 4 (fn-ris-produced-step-with-effects ctx fields event snapshot-carry))
         (mv-nth 2 (fn-replay-identity-effects ctx event)))
  (equal (mv-nth 5 (fn-ris-produced-step-with-effects ctx fields event snapshot-carry))
         (let ((effect (mv-nth 1 (fn-replay-identity-effects ctx event)))
               (child (mv-nth 2 (fn-replay-identity-effects ctx event))))
          (if (equal effect :verdict)
           (list (length (fn-stxe-msgid child)) (len (fn-stxe-detail child))
                 (len (fn-stxe-profile child))) nil))))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-ris-produced-step-is-public-replay
        fn-rpe-produced-complete-result-refines-public)
  :in-theory (e/d (fn-ris-produced-step fn-ris-produced-step-with-effects
                   fn-replay-identity-produced-effects)
                  (fn-rpe-produced-effects fn-replay-identity-step
                   fn-replay-identity-effects fn-ics-carriesp fn-scs-carryp
                   fn-rips-verdict-carry fn-ics-fields fn-scs-cons
                   fn-stxe-msgid fn-stxe-detail fn-stxe-profile length len)))))
