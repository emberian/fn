; Actual replay decision plus same-parser child carries. Funding is separate.
(in-package "ACL2")
(include-book "replay-identity-produced")
(include-book "identity-context-size")
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
(defun fn-ris-produced-step (ctx fields event snapshot-carry)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (checked effect child sizes)
  (fn-replay-identity-produced-effects ctx event)
  (let ((child-carry (cond ((equal effect :snapshot) snapshot-carry)
                           ((equal effect :verdict) (fn-rips-verdict-carry child sizes))
                           (t nil))))
   (if (or (not (fn-ics-carriesp fields))
           (and (not (equal effect :none)) (not (fn-scs-carryp child-carry))))
    (mv checked nil :unavailable)
    (mv checked
     (fn-ics-fields checked
      (if (equal effect :snapshot) (fn-scs-cons child-carry (fn-ics-field 2 fields))
       (fn-ics-field 2 fields))
      (if (equal effect :verdict) (fn-scs-cons child-carry (fn-ics-field 3 fields))
       (fn-ics-field 3 fields))) :carried)))))
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
(verify-guards fn-ris-produced-step)
(defthm fn-ris-produced-step-is-public-replay
 (equal (mv-nth 0 (fn-ris-produced-step ctx fields event snapshot-carry))
        (fn-replay-identity-step ctx event))
 :rule-classes nil
 :hints (("Goal"
 :use (fn-replay-identity-produced-has-original-context-and-effects
       fn-replay-identity-effects-context-is-original-by-definition)
 :in-theory (e/d (fn-ris-produced-step)
  (fn-replay-identity-produced-effects fn-replay-identity-effects
   fn-replay-identity-step fn-ics-carriesp fn-scs-carryp
   fn-rips-verdict-carry fn-ics-fields fn-scs-cons)))))
