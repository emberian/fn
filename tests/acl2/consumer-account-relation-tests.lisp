(in-package "ACL2")
(include-book "../../books/consumer-account-relation")

(defconst *caart-32* (make-list 32 :initial-element 9))
(defconst *caart-16* (make-list 16 :initial-element 8))
(defun fn-caart-event (s txid op)
  (list :consumer-authority (fn-cp-nth 3 s) txid 0 op))
(defun fn-caart-next (s txid op)
  (fn-cp-nth 1 (fn-caa-step s (fn-caart-event s txid op))))
(defun fn-caart-prep (s)
  (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 6 s))))
(defun fn-caart-row (name birth)
  (list :authority-row '(65) 0 name birth *caart-32* *caart-16*
        *caart-32* *caart-32* *caart-32* 1))
(defun fn-caart-count-op (kind s)
  (let ((p (fn-cp-nth 5 (fn-cp-nth 6 s))))
    (list kind '(65) 0 (fn-cp-nth 3 p) (fn-cp-nth 7 p))))

(defconst *caart-initial* (fn-cp-state *caart-32* *caart-32* 0 1 nil))
(defconst *caart-begun*
  (fn-caart-next *caart-initial* 1 '(:authority-begin (65) 0 1 7)))
(defconst *caart-a* (fn-caart-next *caart-begun* 2 (fn-caart-row '(97) 2)))
(defconst *caart-ab* (fn-caart-next *caart-a* 3 (fn-caart-row '(98) 3)))
(defconst *caart-sealed*
  (fn-caart-next *caart-ab* 4 (fn-caart-count-op :authority-seal *caart-ab*)))
(defconst *caart-prepared*
  (fn-caart-next *caart-sealed* 5 '(:authority-prepare (65) 0)))
(defconst *caart-ready*
  (fn-caart-next *caart-prepared* 6 '(:authority-prepare (65) 0)))
(defconst *caart-fence-event*
  (fn-caart-event *caart-ready* 7 (fn-caart-count-op :authority-fence *caart-ready*)))
(defconst *caart-published* (fn-caa-step *caart-ready* *caart-fence-event*))
(defconst *caart-root* (fn-cp-nth 2 *caart-published*))
(defconst *caart-authority* (fn-cp-nth 6 (fn-cp-nth 1 *caart-published*)))
(defconst *caart-rows* (fn-cp-nth 4 *caart-authority*))
(defconst *caart-watermark* (fn-cp-nth 2 *caart-authority*))

;@positive fn-caar-empty-root-establishes-relation
(assert-event
 (and (natp 7) (<= 7 7)
      (fn-caar-root-relp nil 1 (fn-caa-root 7 nil nil))
      (fn-caar-preparation-relp (fn-caart-prep *caart-begun*))
      (fn-caar-preparation-relp (fn-caart-prep *caart-a*))
      (fn-caar-preparation-relp (fn-caart-prep *caart-ab*))
      (fn-caar-preparation-relp (fn-caart-prep *caart-sealed*))))

;@positive fn-caar-prepare-preserves-complete-relation
(assert-event
 (let* ((s *caart-sealed*) (a (fn-cp-nth 6 s))
        (event (fn-caart-event s 5 '(:authority-prepare (65) 0)))
        (one (fn-caa-prepare s a event)))
   (and (fn-caar-preparation-relp (fn-cp-nth 5 (fn-cp-nth 5 a)))
        (equal (car one) :ok)
        (fn-caar-preparation-relp (fn-caart-prep (fn-cp-nth 1 one)))
        (equal (fn-cp-nth 1 (fn-caart-prep (fn-cp-nth 1 one))) :reverse)
        (equal (len (fn-cp-nth 3 (fn-caart-prep (fn-cp-nth 1 one)))) 1)
        (equal (len (fn-cp-nth 4 (fn-caart-prep (fn-cp-nth 1 one)))) 1))))

;@positive fn-caar-prepare-preserves-complete-relation
(assert-event
 (let* ((s *caart-prepared*) (a (fn-cp-nth 6 s))
        (event (fn-caart-event s 6 '(:authority-prepare (65) 0)))
        (one (fn-caa-prepare s a event)))
   (and (fn-caar-preparation-relp (fn-cp-nth 5 (fn-cp-nth 5 a)))
        (equal (car one) :ok)
        (fn-caar-preparation-relp (fn-caart-prep (fn-cp-nth 1 one)))
        (equal (fn-cp-nth 1 (fn-caart-prep (fn-cp-nth 1 one))) :ready))))

;@positive fn-caar-fence-publishes-complete-root
(assert-event
 (let* ((s *caart-ready*) (a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
        (prep (fn-cp-nth 5 p))
        (one (fn-caa-fence s a *caart-fence-event* (fn-cp-nth 4 *caart-fence-event*)))
        (authority (fn-cp-nth 6 (fn-cp-nth 1 one))))
   (and (fn-caar-preparation-relp prep)
        (equal (fn-cp-nth 4 p) (fn-cp-nth 7 prep))
        (equal (car one) :ok)
        (fn-caar-root-relp (fn-cp-nth 4 authority) (fn-cp-nth 2 authority)
                           (fn-cp-nth 2 one))
        (fn-caar-installed-relp *caart-rows* *caart-watermark* *caart-root*
                                (fn-caa-root-auth-config *caart-root*))
        (equal (len *caart-rows*) 2)
        (equal (fn-auth-cred-name (car (fn-cp-nth 3 *caart-root*))) '(97))
        (equal (fn-auth-cred-name (cadr (fn-cp-nth 3 *caart-root*))) '(98)))))

; Corrupted-state refuters, not reachable lifecycle counterexamples.
; Every row still resolves when an extra trie binding is added. Completeness
; must nevertheless reject that root, even if the extra login is inactive.
(assert-event
 (let* ((index (fn-cp-nth 2 *caart-root*))
        (extra (fn-cai-put-octets '(99) '(:account-binding bogus nil) index))
        (bad (fn-caa-root 7 extra (fn-cp-nth 3 *caart-root*))))
   (and (fn-caar-rowsp *caart-rows* extra *caart-watermark*)
        (not (fn-caar-root-relp *caart-rows* *caart-watermark* bad)))))

(assert-event
 (let* ((index (fn-cp-nth 2 *caart-root*))
        (a (fn-cai-get-octets '(97) index))
        (b (fn-cai-get-octets '(98) index))
        (wrong-credential (list :account-binding (fn-cp-nth 1 a) (fn-cp-nth 2 b)))
        (wrong-descriptor
         (list :account-binding (update-nth 4 '(0) (fn-cp-nth 1 a)) (fn-cp-nth 2 a))))
   (and (fn-caar-bindingp (car *caart-rows*) a *caart-watermark*)
        (not (fn-caar-bindingp (car *caart-rows*) wrong-credential *caart-watermark*))
        (not (fn-caar-bindingp (fn-cp-nth 1 wrong-descriptor)
                               wrong-descriptor *caart-watermark*))
        (not (fn-caar-root-relp *caart-rows* *caart-watermark*
                                (fn-caa-root 7 index nil)))
        (not (fn-caar-root-relp (cdr *caart-rows*) *caart-watermark* *caart-root*))
        (not (fn-caar-root-relp (reverse *caart-rows*) *caart-watermark* *caart-root*))
        (not (fn-caar-installed-relp *caart-rows* *caart-watermark* *caart-root*
                                     (fn-auth-make-config nil nil nil nil))))))

;@hypothesis-removal fn-caar-prepare-preserves-complete-relation relation
; Corrupted prepared credentials are retained by the real next tick.
(assert-event
 (let* ((s *caart-prepared*) (a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
        (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
        (bad-prep (update-nth 5 (update-nth 3 nil root) prep))
        (bad-a (update-nth 5 (update-nth 5 bad-prep p) a))
        (one (fn-caa-prepare s bad-a
                             (fn-caart-event s 6 '(:authority-prepare (65) 0)))))
   (and (not (fn-caar-preparation-relp (fn-cp-nth 5 (fn-cp-nth 5 bad-a))))
        (equal (car one) :ok)
        (not (fn-caar-preparation-relp (fn-caart-prep (fn-cp-nth 1 one)))))))

;@hypothesis-removal fn-caar-prepare-preserves-complete-relation success
(assert-event
 (let* ((s *caart-ready*) (a (fn-cp-nth 6 s))
        (one (fn-caa-prepare s a (fn-caart-event s 7 '(:authority-prepare (65) 0)))))
   (and (fn-caar-preparation-relp (fn-cp-nth 5 (fn-cp-nth 5 a)))
        (not (equal (car one) :ok))
        (not (fn-caar-preparation-relp (fn-caart-prep (fn-cp-nth 1 one)))))))

;@hypothesis-removal fn-caar-empty-root-establishes-relation policy-nat
(assert-event
 (and (not (natp -1)) (<= -1 7)
      (not (fn-caar-root-relp nil 1 (fn-caa-root -1 nil nil)))))
;@hypothesis-removal fn-caar-empty-root-establishes-relation policy-range
(assert-event
 (and (natp 8) (not (<= 8 7))
      (not (fn-caar-root-relp nil 1 (fn-caa-root 8 nil nil)))))

;@hypothesis-removal fn-caar-fence-publishes-complete-root relation
; Corrupted state: a fence does not repair missing installed credentials.
(assert-event
 (let* ((s *caart-ready*) (a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
        (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
        (bad-prep (update-nth 5 (update-nth 3 nil root) prep))
        (bad-p (update-nth 5 bad-prep p)) (bad-a (update-nth 5 bad-p a))
        (one (fn-caa-fence s bad-a *caart-fence-event*
                           (fn-cp-nth 4 *caart-fence-event*)))
        (authority (fn-cp-nth 6 (fn-cp-nth 1 one))))
   (and (not (fn-caar-preparation-relp (fn-cp-nth 5 bad-p)))
        (equal (fn-cp-nth 4 bad-p) (fn-cp-nth 7 (fn-cp-nth 5 bad-p)))
        (equal (car one) :ok)
        (not (fn-caar-root-relp (fn-cp-nth 4 authority) (fn-cp-nth 2 authority)
                                (fn-cp-nth 2 one))))))

;@hypothesis-removal fn-caar-fence-publishes-complete-root watermark
; Corrupted pending watermark makes the very same creation tokens invalid.
(assert-event
 (let* ((s *caart-ready*) (a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
        (bad-p (update-nth 4 1 p)) (bad-a (update-nth 5 bad-p a))
        (one (fn-caa-fence s bad-a *caart-fence-event*
                           (fn-cp-nth 4 *caart-fence-event*)))
        (authority (fn-cp-nth 6 (fn-cp-nth 1 one))))
   (and (fn-caar-preparation-relp (fn-cp-nth 5 bad-p))
        (not (equal (fn-cp-nth 4 bad-p) (fn-cp-nth 7 (fn-cp-nth 5 bad-p))))
        (equal (car one) :ok)
        (not (fn-caar-root-relp (fn-cp-nth 4 authority) (fn-cp-nth 2 authority)
                                (fn-cp-nth 2 one))))))

;@hypothesis-removal fn-caar-fence-publishes-complete-root success
(assert-event
 (let* ((s *caart-prepared*) (a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
        (one (fn-caa-fence s a *caart-fence-event*
                           (fn-cp-nth 4 *caart-fence-event*)))
        (authority (fn-cp-nth 6 (fn-cp-nth 1 one))))
   (and (fn-caar-preparation-relp (fn-cp-nth 5 p))
        (equal (fn-cp-nth 4 p) (fn-cp-nth 7 (fn-cp-nth 5 p)))
        (not (equal (car one) :ok))
        (not (fn-caar-root-relp (fn-cp-nth 4 authority) (fn-cp-nth 2 authority)
                                (fn-cp-nth 2 one))))))

;@positive fn-caar-seal-preserves-complete-relation
(assert-event
 (let* ((s *caart-ab*) (a (fn-cp-nth 6 s))
        (op (fn-caart-count-op :authority-seal s))
        (one (fn-caa-seal s a (fn-caart-event s 4 op) op)))
   (and (fn-caar-preparation-relp (fn-cp-nth 5 (fn-cp-nth 5 a)))
        (equal (car one) :ok)
        (fn-caar-preparation-relp (fn-caart-prep (fn-cp-nth 1 one))))))

;@hypothesis-removal fn-caar-seal-preserves-complete-relation relation
; Corrupted state: seal preserves an extra trie entry, so complete coverage
; must already have been established by the stage producer.
(assert-event
 (let* ((s *caart-ab*) (a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a))
        (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
        (extra (fn-cai-put-octets '(99) '(:account-binding bogus nil) (fn-cp-nth 2 root)))
        (bad-prep (update-nth 5 (update-nth 2 extra root) prep))
        (bad-a (update-nth 5 (update-nth 5 bad-prep p) a))
        (op (fn-caart-count-op :authority-seal s))
        (one (fn-caa-seal s bad-a (fn-caart-event s 4 op) op)))
   (and (not (fn-caar-preparation-relp (fn-cp-nth 5 (fn-cp-nth 5 bad-a))))
        (equal (car one) :ok)
        (not (fn-caar-preparation-relp (fn-caart-prep (fn-cp-nth 1 one)))))))

;@hypothesis-removal fn-caar-seal-preserves-complete-relation success
(assert-event
 (let* ((s *caart-sealed*) (a (fn-cp-nth 6 s))
        (op (fn-caart-count-op :authority-seal s))
        (one (fn-caa-seal s a (fn-caart-event s 5 op) op)))
   (and (fn-caar-preparation-relp (fn-cp-nth 5 (fn-cp-nth 5 a)))
        (not (equal (car one) :ok))
        (not (fn-caar-preparation-relp (fn-caart-prep (fn-cp-nth 1 one)))))))

; Reachable deletion adoption retains the tombstone in the exact trie while
; removing its credential from the actually prepared authentication list.
(defun fn-caart-current-count-op (kind s)
  (let ((p (fn-cp-nth 5 (fn-cp-nth 6 s))))
    (list kind (fn-cp-nth 1 p) (fn-cp-nth 2 p)
          (fn-cp-nth 3 p) (fn-cp-nth 7 p))))
(defconst *caart-delete-begin*
  (fn-caart-next (fn-cp-nth 1 *caart-published*) 8
                 '(:authority-begin (66) 1 4 7)))
(defconst *caart-delete-a*
  (fn-caart-next *caart-delete-begin* 9
                 (update-nth 2 1 (update-nth 1 '(66) (fn-caart-row '(97) 2)))))
(defconst *caart-delete-b*
  (fn-caart-next *caart-delete-a* 10 '(:authority-tombstone (66) 1 (98) 3)))
(defconst *caart-delete-sealed*
  (fn-caart-next *caart-delete-b* 11
                 (fn-caart-current-count-op :authority-seal *caart-delete-b*)))
(defconst *caart-delete-prepared*
  (fn-caart-next *caart-delete-sealed* 12 '(:authority-prepare (66) 1)))
(defconst *caart-delete-ready*
  (fn-caart-next *caart-delete-prepared* 13 '(:authority-prepare (66) 1)))
(defconst *caart-delete-published*
  (fn-caa-step *caart-delete-ready*
               (fn-caart-event *caart-delete-ready* 14
                (fn-caart-current-count-op :authority-fence *caart-delete-ready*))))

;@positive fn-caar-prepare-preserves-complete-relation
(assert-event
 (let* ((s *caart-delete-sealed*) (a (fn-cp-nth 6 s))
        (one (fn-caa-prepare s a (fn-caart-event s 12 '(:authority-prepare (66) 1))))
        (prep (fn-caart-prep (fn-cp-nth 1 one))))
   (and (fn-caar-preparation-relp (fn-cp-nth 5 (fn-cp-nth 5 a)))
        (equal (car one) :ok)
        (fn-caar-preparation-relp prep)
        (not (fn-cp-nth 3 (car (fn-cp-nth 4 prep))))
        (null (fn-cp-nth 3 (fn-cp-nth 5 prep))))))

(assert-event
 (let* ((one *caart-delete-published*) (root (fn-cp-nth 2 one))
        (a (fn-cp-nth 6 (fn-cp-nth 1 one))) (rows (fn-cp-nth 4 a))
        (binding (fn-cai-get-octets '(98) (fn-cp-nth 2 root))))
   (and (eq (car one) :ok)
        (fn-caar-installed-relp rows (fn-cp-nth 2 a) root (fn-caa-root-auth-config root))
        (equal (len rows) 2) (equal (len (fn-cp-nth 3 root)) 1)
        (equal (fn-cp-nth 2 (car rows)) (fn-cp-nth 2 (car *caart-rows*)))
        (equal (fn-cp-nth 2 (cadr rows)) (fn-cp-nth 2 (cadr *caart-rows*)))
        (equal (fn-cp-nth 1 binding) (cadr rows))
        (null (fn-cp-nth 2 binding))
        (null (fn-caa-current-binding '(98) root)))))

;@positive fn-caar-lookup-belongs-to-adopted-rows
;@positive fn-caar-any-lookup-belongs-to-adopted-rows
;@positive fn-caar-current-binding-is-adopted-live-account
(assert-event
 (let* ((name '(97)) (root *caart-root*) (rows *caart-rows*)
        (watermark *caart-watermark*)
        (binding (fn-cai-get-octets name (fn-cp-nth 2 root)))
        (current (fn-caa-current-binding name root)) (row (fn-cp-nth 1 binding)))
   (and (fn-caar-root-relp rows watermark root)
        (fn-cbor-octet-listp name) binding current (equal current binding)
        (member-equal row rows) (equal (fn-cp-nth 1 row) name)
        (fn-cp-nth 3 row) (fn-caar-bindingp row binding watermark))))

; Tombstones are still produced bindings, but never current live accounts.
;@positive fn-caar-lookup-belongs-to-adopted-rows
;@positive fn-caar-any-lookup-belongs-to-adopted-rows
(assert-event
 (let* ((one *caart-delete-published*) (root (fn-cp-nth 2 one))
        (a (fn-cp-nth 6 (fn-cp-nth 1 one))) (rows (fn-cp-nth 4 a))
        (watermark (fn-cp-nth 2 a)) (name '(98))
        (binding (fn-cai-get-octets name (fn-cp-nth 2 root))) (row (fn-cp-nth 1 binding)))
   (and (fn-caar-root-relp rows watermark root) (fn-cbor-octet-listp name) binding
        (member-equal row rows) (equal (fn-cp-nth 1 row) name)
        (fn-caar-bindingp row binding watermark)
        (null (fn-cp-nth 3 row)) (null (fn-caa-current-binding name root)))))

;@hypothesis-removal fn-caar-lookup-belongs-to-adopted-rows octets
; The actual total lookup drops an improper tail. Membership remains true,
; but exact equality to the malformed original requested name fails.
;@positive fn-caar-any-lookup-belongs-to-adopted-rows
(assert-event
 (let* ((name '(97 . 777)) (root *caart-root*) (rows *caart-rows*)
        (watermark *caart-watermark*)
        (binding (fn-cai-get-octets name (fn-cp-nth 2 root))) (row (fn-cp-nth 1 binding)))
   (and (fn-caar-root-relp rows watermark root) binding
        (not (fn-cbor-octet-listp name))
        (member-equal row rows) (fn-caar-bindingp row binding watermark)
        (not (and (member-equal row rows) (equal (fn-cp-nth 1 row) name)
                  (fn-caar-bindingp row binding watermark))))))

; Corrupted-state binding is individually valid but never adopted.
(defconst *caart-extra-binding*
 (let ((a (fn-cai-get-octets '(97) (fn-cp-nth 2 *caart-root*))))
   (list :account-binding (update-nth 1 '(99) (fn-cp-nth 1 a))
         (update-nth 1 '(99) (fn-cp-nth 2 a)))))
(defconst *caart-extra-root*
 (fn-caa-root 7 (fn-cai-put-octets '(99) *caart-extra-binding* (fn-cp-nth 2 *caart-root*))
              (fn-cp-nth 3 *caart-root*)))

;@hypothesis-removal fn-caar-lookup-belongs-to-adopted-rows relation
;@hypothesis-removal fn-caar-any-lookup-belongs-to-adopted-rows relation
;@hypothesis-removal fn-caar-current-binding-is-adopted-live-account relation
(assert-event
 (let* ((name '(99)) (root *caart-extra-root*) (rows *caart-rows*)
        (watermark *caart-watermark*)
        (binding (fn-cai-get-octets name (fn-cp-nth 2 root)))
        (current (fn-caa-current-binding name root)) (row (fn-cp-nth 1 binding)))
   (and (not (fn-caar-root-relp rows watermark root))
        (fn-cbor-octet-listp name) binding current (equal current binding)
        (equal (fn-cp-nth 1 row) name) (fn-cp-nth 3 row)
        (fn-caar-bindingp row binding watermark)
        (not (and (member-equal row rows) (fn-caar-bindingp row binding watermark)))
        (not (and (member-equal row rows) (equal (fn-cp-nth 1 row) name)
                  (fn-caar-bindingp row binding watermark)))
        (not (and (member-equal row rows) (equal (fn-cp-nth 1 row) name)
                  (fn-cp-nth 3 row) (fn-caar-bindingp row binding watermark))))))

;@hypothesis-removal fn-caar-lookup-belongs-to-adopted-rows hit
;@hypothesis-removal fn-caar-any-lookup-belongs-to-adopted-rows hit
;@hypothesis-removal fn-caar-current-binding-is-adopted-live-account live-hit
(assert-event
 (let* ((name '(99)) (root *caart-root*) (rows *caart-rows*)
        (watermark *caart-watermark*)
        (binding (fn-cai-get-octets name (fn-cp-nth 2 root)))
        (current (fn-caa-current-binding name root)) (row (fn-cp-nth 1 binding)))
   (and (fn-caar-root-relp rows watermark root) (fn-cbor-octet-listp name)
        (null binding) (null current) (equal current binding)
        (not (and (member-equal row rows) (fn-caar-bindingp row binding watermark)))
        (not (and (member-equal row rows) (equal (fn-cp-nth 1 row) name)
                  (fn-caar-bindingp row binding watermark)))
        (not (and (member-equal row rows) (equal (fn-cp-nth 1 row) name)
                  (fn-cp-nth 3 row) (fn-caar-bindingp row binding watermark))))))
