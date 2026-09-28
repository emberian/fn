; Teeth for books/node-secret.lisp (SEC-006, PRF-210): the BLAKE3 purpose-key
; derivation and MAC against the Rust blake3 crate, the info-label
; separation fn-ns-purpose-inputs-separate-by-definition with a witness and
; the removal of its hypothesis, and the key file's round trip
; fn-ns-file-parse-of-render.
(in-package "ACL2")
(include-book "../../books/node-secret")
(include-book "must-fail-checked")

(defun nst-codes (cs)
  (if (consp cs) (cons (char-code (car cs)) (nst-codes (cdr cs))) nil))
(defun nst-octets (s) (nst-codes (coerce s 'list)))
(defun nst-hex (octets)
  (if (consp octets)
      (let ((d "0123456789abcdef"))
        (concatenate 'string (string (char d (floor (car octets) 16)))
                     (string (char d (mod (car octets) 16)))
                     (nst-hex (cdr octets))))
    ""))
(defun nst-range (lo hi) (declare (xargs :measure (nfix (- hi lo))))
  (if (and (natp lo) (natp hi) (< lo hi)) (cons lo (nst-range (1+ lo) hi)) nil))

; The derivation against an independent implementation: the values below are
; the Rust `blake3' crate's (the Python `blake3' package 1.x over it,
; derive_key_context / key=), not this tree's.  The purpose key is BLAKE3
; derive_key under the info label with ROOT || IDENTITY as the material, and
; the MAC is keyed_hash under the purpose key.
(defconst *nst-root7* (make-list 32 :initial-element 7))
(defconst *nst-root9* (make-list 32 :initial-element 9))
(assert-event
 (equal (nst-hex (fn-blake3-derive-key (nst-octets "fn/cancel-lock/v2")
                                       (append *nst-root7* (nst-octets "hbox.ember.software"))))
        "60f52b6a4767d15cb475d0c3ac76376e19de0762151235c2cb533c5731b50f62"))
(assert-event
 (equal (nst-hex (fn-ns-mac (fn-blake3-derive-key (nst-octets "fn/posting-account/v2")
                                                  (append *nst-root9* (nst-octets "hbox.ember.software")))
                            (nst-octets "alice")))
        "5a74675107b96d06e1d2d127d27eee4910272b51baee042b52790bd3803ca5ee"))

; The info labels are the ones the review names.
(assert-event (equal *fn-ns-cancel-lock-info* (nst-octets "fn/cancel-lock/v2")))
(assert-event (equal *fn-ns-posting-account-info* (nst-octets "fn/posting-account/v2")))
(assert-event (equal (fn-ns-secret-width) 32))

; A ring of two epochs: epoch 2 current, epoch 1 retained.
(defconst *nst-e1* (fn-ns-create-entry (nst-octets "hbox.ember.software")
                                       (make-list 32 :initial-element 7)))
(defconst *nst-e2* (fn-ns-rotate-entry *nst-e1* nil (make-list 32 :initial-element 9)))
(defconst *nst-ring* (list *nst-e2* *nst-e1*))
(assert-event (and (fn-ns-entryp *nst-e1*) (fn-ns-entryp *nst-e2*)
                   (equal (fn-ns-entry-epoch *nst-e1*) 1)
                   (equal (fn-ns-entry-epoch *nst-e2*) 2)
                   (equal (fn-ns-entry-identity *nst-e2*) (nst-octets "hbox.ember.software"))
                   (fn-ns-ringp *nst-ring*)
                   (not (fn-ns-ringp (list *nst-e1* *nst-e2*)))   ; epochs must decrease
                   (not (fn-ns-ringp nil))))
; The default identity.
(assert-event (equal (fn-ns-entry-identity (fn-ns-create-entry nil (make-list 32 :initial-element 7)))
                     (nst-octets "local")))

; The purpose keys the node derives are the reference values above: the
; entry's key material is ROOT || IDENTITY and the context is the label.
(assert-event
 (and (equal (nst-hex (fn-ns-cancel-lock-key *nst-e1*))
             "60f52b6a4767d15cb475d0c3ac76376e19de0762151235c2cb533c5731b50f62")
      (equal (nst-hex (fn-ns-posting-account-mac *nst-ring* (nst-octets "alice")))
             "5a74675107b96d06e1d2d127d27eee4910272b51baee042b52790bd3803ca5ee")))

; fn-ns-purpose-inputs-separate-by-definition.  Witness: the two labels the
; node uses, under one entry, and the purpose keys they give.
(assert-event
 (and (not (equal *fn-ns-cancel-lock-info* *fn-ns-posting-account-info*))
      (not (equal (fn-ns-purpose-input *nst-e2* *fn-ns-cancel-lock-info*)
                  (fn-ns-purpose-input *nst-e2* *fn-ns-posting-account-info*)))
      (not (equal (fn-ns-cancel-lock-key *nst-e2*) (fn-ns-posting-account-key *nst-ring*)))))
; Removal of "distinct": equal labels give the same input, and the same key.
(assert-event
 (and (equal (fn-ns-purpose-input *nst-e2* *fn-ns-cancel-lock-info*)
             (fn-ns-purpose-input *nst-e2* *fn-ns-cancel-lock-info*))
      (equal (fn-ns-purpose-key *nst-e2* *fn-ns-cancel-lock-info*)
             (fn-ns-cancel-lock-key *nst-e2*))))
(must-fail-checked
 (defthm nst-separation-needs-distinct-labels
   (not (equal (fn-ns-purpose-input entry i1) (fn-ns-purpose-input entry i2)))))

; The derived keys are bound to the node identity and the epoch: another
; identity or another root gives another key.
(assert-event
 (and (not (equal (fn-ns-cancel-lock-key *nst-e1*)
                  (fn-ns-cancel-lock-key (fn-ns-make-entry 1 (nst-octets "other")
                                                           (make-list 32 :initial-element 7)))))
      (not (equal (fn-ns-cancel-lock-key *nst-e1*) (fn-ns-cancel-lock-key *nst-e2*)))))

; fn-ns-file-parse-of-render: witness, and the parse refuses what is not a
; v1 file of one entry.
(defconst *nst-file* (fn-ns-file-render *nst-e2*))
(assert-event (and (fn-ns-entryp *nst-e2*)
                   (equal (len *nst-file*) (+ 18 4 2 19 32))
                   (equal (fn-ns-file-parse *nst-file*) *nst-e2*)))
(assert-event (null (fn-ns-file-parse (cdr *nst-file*))))                 ; bad magic
(assert-event (null (fn-ns-file-parse (append *nst-file* '(0)))))         ; 33-octet root
(assert-event (null (fn-ns-file-parse (butlast *nst-file* 1))))           ; 31-octet root
(assert-event (null (fn-ns-file-parse (make-list 61 :initial-element 0))))
; Removal of fn-ns-entryp: a v1 file naming epoch 0 is no entry, and the
; parse refuses it.
(assert-event
 (let ((e (fn-ns-make-entry 0 nil (make-list 32 :initial-element 7))))
   (and (not (fn-ns-entryp e))
        (null (fn-ns-file-parse (append *fn-ns-file-magic* '(0 0 0 0) '(0 0)
                                        (make-list 32 :initial-element 7)))))))
