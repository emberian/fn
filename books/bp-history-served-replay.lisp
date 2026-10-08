; Journal replay over the same carried history used by individual live steps.
(in-package "ACL2")
(include-book "bp-native-app-fast")

; This loop threads the joined state and stops at the first refused step;
; no list of intermediate states is built. Existing BP decisions are total
; ACL2 functions with unverified guards; EC-CALL uses their safe execution
; counterparts, including the already-served indexed step, never a disk reader.
(defun fn-bpaj-replay-rest-served (joined store records fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t
                  :measure (acl2-count records)))
  (if (atom records) (list t joined)
    (let ((answer (ec-call (fn-bpaj-apply-record-fast joined store (car records) fn-arena fn-hist))))
      (if (not (car answer)) (list nil joined)
        (fn-bpaj-replay-rest-served (ec-call (fn-bpaj-nth 1 answer)) store (cdr records)
                                    fn-arena fn-hist)))))

(defthm fn-bpaj-replay-rest-served-is-reference
  (implies (and (fn-bpaj-statep joined) (fn-sn-statep store)
                (fn-hist-of-storep hist store))
           (equal (fn-bpaj-replay-rest-served joined store records arena hist)
                  (fn-bpaj-replay-rest joined store records arena)))
  :hints (("Goal" :induct (fn-bpaj-replay-rest joined store records arena)
           :in-theory '(fn-bpaj-replay-rest fn-bpaj-replay-rest-served
                         fn-bpaj-apply-record-fast-is-checked
                         fn-bpaj-apply-record-preserves-statep))))

(defun fn-bpaj-replay-served (store records fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (if (or (atom records) (not (ec-call (fn-bprr-configp (car records)))))
      (list nil nil)
    (let ((receiver (ec-call (fn-bpr-initial-state (ec-call (fn-bprr-config (car records)))))))
      (if (not (ec-call (fn-bpr-statep receiver))) (list nil nil)
        (fn-bpaj-replay-rest-served (ec-call (fn-bpaj-make-state receiver nil nil nil))
                                    store (cdr records) fn-arena fn-hist)))))

(defthm fn-bpaj-replay-served-is-reference
  (implies (and (fn-sn-statep store) (fn-hist-of-storep hist store))
           (equal (fn-bpaj-replay-served store records arena hist)
                  (fn-bpaj-replay store records arena)))
  :hints (("Goal"
 :use ((:instance fn-bpaj-replay-rest-served-is-reference
          (joined (fn-bpaj-make-state (fn-bpr-initial-state (fn-bprr-config (car records))) nil nil nil))
          (records (cdr records))))
 :in-theory (union-theories (theory 'minimal-theory)
   '(fn-bpaj-replay-served fn-bpaj-replay fn-bpaj-statep-of-constructor
     fn-bpaj-intent-listp fn-bpaj-fact-listp car-cons cdr-cons)))))

(in-theory (disable fn-bpaj-replay-rest-served fn-bpaj-replay-served))
