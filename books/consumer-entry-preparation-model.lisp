; Proof-only entry cursor denotation and metadata relation. None runs on a
; served preparation/fence; actual runtime tick is one inspected/rebuilt cell.
(in-package "ACL2")
(include-book "consumer-entry-preparation")
(include-book "consumer-account-metadata")

(defun fn-cepm-denotation (cursor)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((key (fn-cp-nth 1 cursor)) (remaining (fn-cp-nth 2 cursor))
        (reversed (fn-cp-nth 4 cursor)) (phase (fn-cp-nth 6 cursor))
        (rebuilt (fn-cp-nth 7 cursor)) (old (fn-cp-nth 9 cursor)))
  (cond ((eq phase :seek)
         (list (revappend reversed (fn-cp-remove key remaining))
               (fn-cp-find key remaining)))
        ((eq phase :reverse) (list (revappend reversed rebuilt) old))
        ((eq phase :ready) (list rebuilt old))
        (t nil))))

(defthm fn-cepm-actual-tick-preserves-selected-entry-and-removal
 (equal (fn-cepm-denotation (fn-cp-nth 1 (fn-cep-tick cursor)))
        (fn-cepm-denotation cursor))
 :hints (("Goal" :in-theory
  (e/d (fn-cepm-denotation fn-cep-tick fn-cep-state fn-cp-nth
        fn-cp-remove fn-cp-find revappend)
       (revappend-removal fn-caac-list-cons)))))

(defthm fn-cepm-begin-establishes-exact-selected-entry-and-removal
 (implies (fn-cpm-metadatap metadata)
  (equal (fn-cepm-denotation (fn-cp-nth 1 (fn-cep-begin cp op metadata)))
         (list (fn-cp-remove (fn-cep-operation-key op) (fn-cp-nth 5 cp))
               (fn-cp-find (fn-cep-operation-key op) (fn-cp-nth 5 cp)))))
 :hints (("Goal" :in-theory
  (e/d (fn-cepm-denotation fn-cep-begin fn-cep-state fn-cp-nth)
       (fn-cpm-metadatap fn-cep-operation-key fn-cp-remove fn-cp-find
        revappend-removal)))))

(defun fn-cepm-metadata-relp (cursor)
 (declare (xargs :guard t :verify-guards nil))
 (and (true-listp (fn-cp-nth 2 cursor))
      (true-listp (fn-cp-nth 4 cursor))
      (true-listp (fn-cp-nth 7 cursor))
      (equal (fn-cp-nth 3 cursor) (fn-caam-list-annotation (fn-cp-nth 2 cursor)))
      (equal (fn-cp-nth 5 cursor) (fn-caam-list-annotation (fn-cp-nth 4 cursor)))
      (equal (fn-cp-nth 8 cursor) (fn-caam-list-annotation (fn-cp-nth 7 cursor)))))

(defthm fn-cepm-actual-tick-maintains-entry-annotations
 (implies (fn-cepm-metadata-relp cursor)
          (fn-cepm-metadata-relp (fn-cp-nth 1 (fn-cep-tick cursor))))
 :hints (("Goal"
  :use ((:instance fn-caam-list-cons-maintains-annotation
          (tail (fn-cp-nth 4 cursor)) (tail-metadata (fn-cp-nth 5 cursor))
          (head (car (fn-cp-nth 2 cursor)))
          (head-carry (fn-cp-nth 1 (fn-cp-nth 3 cursor))))
        (:instance fn-caam-list-cons-maintains-annotation
          (tail (fn-cp-nth 7 cursor)) (tail-metadata (fn-cp-nth 8 cursor))
          (head (car (fn-cp-nth 4 cursor)))
          (head-carry (fn-cp-nth 1 (fn-cp-nth 5 cursor)))))
  :in-theory
   (e/d (fn-cepm-metadata-relp fn-cep-tick fn-cep-state fn-cp-nth
         fn-caam-list-annotation)
        (fn-caac-list-cons fn-scs-summary fn-caam-list-cons-maintains-annotation)))))

(in-theory (disable fn-cepm-denotation fn-cepm-metadata-relp))
