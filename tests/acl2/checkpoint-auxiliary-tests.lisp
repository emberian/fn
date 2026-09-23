(in-package "ACL2")
(include-book "../../books/checkpoint-auxiliary")
(include-book "../../books/store-observed")
(include-book "../../books/hybrid-store")
(include-book "../../books/codec-attach")

; The selected pack keeps exact bootstrap, article, keyring-snapshot and
; unbound standalone-verdict bytes.  The latter is not an accepted composite
; verdict and must not be promoted to historical authority on reopen.
; Reclamation may leave only the rollover in the physical suffix; its original
; dense sequence remains 4, and the old incarnation is fenced.
(defconst *cpa-bootstrap*
  (fn-cpe-make 0 0 0 (list :bootstrap '(104 105 115 116) '(111 108 100))))
(defconst *cpa-article*
  (fn-record-make 1 1 1 "<preserve@example.invalid>" '(97 13 10)
                  '("fn.letters") "obligation" "subject" "evidence" 3 841000000))
(defconst *cpa-snapshot*
  (fn-stxk-make 2 2 2 1 '(111 112 97 113 117 101 45 118 49) '(1 2 3)))
(defconst *cpa-verdict*
  (fn-stxe-make 3 3 3 "<preserve@example.invalid>" :unverified '(1) 1
                '(111 112 97 113 117 101 45 118 49)))
(defconst *cpa-rollover*
  (fn-cpe-make 4 4 4 (list :rollover '(110 101 119))))
(make-event `(defconst *cpa-raw-bootstrap*
               ',(fn-store-event-encode *cpa-bootstrap*)))
(make-event `(defconst *cpa-raw-article*
               ',(fn-store-event-encode *cpa-article*)))
(make-event `(defconst *cpa-raw-snapshot*
               ',(fn-store-event-encode *cpa-snapshot*)))
(make-event `(defconst *cpa-raw-verdict*
               ',(fn-store-event-encode *cpa-verdict*)))
(make-event `(defconst *cpa-raw-rollover*
               ',(fn-store-event-encode *cpa-rollover*)))
(defconst *cpa-summary*
  (fn-cc-make 4 4 (list *cpa-raw-bootstrap* *cpa-raw-article*
                        *cpa-raw-snapshot* *cpa-raw-verdict*)))

(assert-event (equal (fn-store-event-decode-exact *cpa-raw-bootstrap*)
                     (list :ok *cpa-bootstrap*)))
(assert-event (equal (fn-store-event-decode-exact *cpa-raw-rollover*)
                     (list :ok *cpa-rollover*)))
(assert-event (equal (fn-store-event-decode-exact *cpa-raw-snapshot*)
                     (list :ok *cpa-snapshot*)))
(assert-event (equal (fn-store-event-decode-exact *cpa-raw-verdict*)
                     (list :ok *cpa-verdict*)))
(assert-event
 (equal (fn-cc-recover-observation *cpa-summary*
                                   (list (list 4 *cpa-raw-rollover*)) 5)
        (list :ok (list *cpa-raw-bootstrap* *cpa-raw-article*
                        *cpa-raw-snapshot* *cpa-raw-verdict*
                        *cpa-raw-rollover*) 5)))
(assert-event
 (equal (fn-cc-decode-exact (fn-cc-encode *cpa-summary*))
        (list :ok *cpa-summary*)))

(make-event `(defconst *cpa-open*
               ',(fn-sn-open-observed '("fn.letters") 32 5
                                      (list *cpa-bootstrap* *cpa-article*
                                            *cpa-snapshot* *cpa-verdict*
                                            *cpa-rollover*))))
(assert-event (fn-sn-open-okp *cpa-open*))
(defconst *cpa-reopened* (fn-sn-open-state *cpa-open*))
(assert-event (equal (fn-cpa-store-auxiliary-agrees *cpa-reopened*)
                     '(:ok 1)))
(assert-event (equal (fn-cp-nth 2 (fn-sn-consumer *cpa-reopened*))
                     '(110 101 119)))
(assert-event (equal (fn-cp-nth 3 (fn-sn-consumer *cpa-reopened*)) 5))
(assert-event (equal (fn-sn-identity-next *cpa-reopened*) 5))
(assert-event (equal (fn-sn-keyring-snapshots *cpa-reopened*)
                     (list *cpa-snapshot*)))
(assert-event (equal (fn-sn-verdicts *cpa-reopened*) nil))
(make-event
 `(defconst *cpa-before-rollover*
    ',(fn-sn-open-observed '("fn.letters") 32 4
                           (list *cpa-bootstrap* *cpa-article*
                                 *cpa-snapshot* *cpa-verdict*))))
(assert-event (fn-sn-open-okp *cpa-before-rollover*))
(assert-event
 (equal (fn-cpa-clone-phase
         (fn-sn-open-state *cpa-before-rollover*) *cpa-rollover*)
        :pending))
(assert-event
 (equal (fn-cpa-clone-phase *cpa-reopened* *cpa-rollover*)
        :completed))
(assert-event
 (equal (fn-cpa-clone-phase-of-octets
         *cpa-reopened* (fn-cpe-encode *cpa-rollover*))
        :completed))
(assert-event
 (equal (fn-cpa-clone-phase
         *cpa-reopened*
         (fn-cpe-make 4 4 4 (list :rollover '(111 108 100))))
        :refused))
(make-event
 `(defconst *cpa-empty-open*
    ',(fn-sn-open-observed '("fn.letters") 32 0 nil)))
(assert-event (fn-sn-open-okp *cpa-empty-open*))
(assert-event
 (equal (fn-cpa-bootstrap-proposal
         (fn-sn-open-state *cpa-empty-open*) '(104) '(105))
        (list :ok (fn-cpe-make 0 0 0 '(:bootstrap (104) (105))))))
(assert-event
 (equal (fn-cpa-bootstrap-proposal *cpa-reopened* '(104) '(105))
        '(:refused :already-bootstrapped)))

(assert-event
 (equal (fn-cpa-rollover-proposal *cpa-reopened* '(110 101 119))
        '(:refused :same-incarnation)))
(assert-event
 (equal (fn-cpa-rollover-proposal *cpa-reopened* nil)
        '(:refused :incarnation-id)))
(assert-event
 (let ((proposal (fn-cpa-rollover-proposal *cpa-reopened* '(110 101 119 50))))
   (and (equal (car proposal) :ok)
        (fn-cpe-eventp (cadr proposal))
        (equal (fn-cpe-sequence (cadr proposal)) 5)
        (equal (fn-cpe-operation (cadr proposal))
               '(:rollover (110 101 119 50))))))

; A malformed recovered projection cannot be mistaken for equality just
; because the checkpoint's article node still matches.
(assert-event
 (equal (fn-cpa-store-auxiliary-agrees
         (fn-sn-with-consumer *cpa-reopened* nil))
        '(:mismatch :auxiliary-state)))
(assert-event
 (equal (fn-cpa-store-auxiliary-agrees
         (update-nth 7 (list (cons "<wrong@example.invalid>" :verified))
                     *cpa-reopened*))
        '(:mismatch :auxiliary-state)))
(assert-event
 (equal (fn-cpa-store-auxiliary-agrees
         (update-nth 8 (list :lost-snapshot) *cpa-reopened*))
        '(:mismatch :auxiliary-state)))
(assert-event
 (equal (fn-cpa-store-auxiliary-agrees
         (update-nth 9 2 *cpa-reopened*))
        '(:mismatch :auxiliary-state)))

; Recovery of a genuinely bound composite keeps a nonempty historical verdict
; and its exact enrolled snapshot.  The two :verified observations here are
; abstract test inputs to the ACL2 constructor, not a native crypto witness.
(defconst *cpa-h-principal* (make-list 32 :initial-element 7))
(defconst *cpa-h-ed* (make-list 32 :initial-element 11))
(defconst *cpa-h-ml* (make-list 1952 :initial-element 13))
(defconst *cpa-h-keys* (list (cons :ed25519 *cpa-h-ed*)
                            (cons :ml-dsa-65 *cpa-h-ml*)))
(defconst *cpa-h-sigs*
  (list (cons :ed25519 (make-list 64 :initial-element 17))
        (cons :ml-dsa-65 (make-list 3309 :initial-element 19))))
(defun cpa-h-line (text)
  (append (fn-record-string-octets text) '(13 10)))
(defconst *cpa-h-source*
  (append (cpa-h-line "From: author@example.invalid")
          (cpa-h-line "Newsgroups: fn.letters")
          (cpa-h-line "Subject: preserved")
          (cpa-h-line "Message-ID: <preserved-hybrid@example.invalid>")
          '(13 10 98 111 100 121 13 10)))
(make-event
 `(defconst *cpa-h-keyring*
    ',(fn-hsig-keyring-event 0 0 0 1 *cpa-h-principal* *cpa-h-keys*)))
(make-event
 `(defconst *cpa-h-event*
    ',(fn-hsig-authorized-submission-event
       1 1 1 1 (fn-stxk-snapshot *cpa-h-keyring*)
       "<preserved-hybrid@example.invalid>" *cpa-h-source*
       '("fn.letters") "obligation" "subject" "release"
       (fn-charge-for-payload (len *cpa-h-source*))
       *cpa-h-principal* *cpa-h-keys* *cpa-h-sigs* *cpa-h-ml*
       :verified :verified (fn-clock-observation 1 841000000000 0 t))))
(assert-event (fn-stxa-p *cpa-h-event*))
(make-event
 `(defconst *cpa-h-raw-keyring* ',(fn-store-event-encode *cpa-h-keyring*)))
(make-event
 `(defconst *cpa-h-raw-event* ',(fn-store-event-encode *cpa-h-event*)))
(defconst *cpa-h-summary*
  (fn-cc-make 2 2 (list *cpa-h-raw-keyring* *cpa-h-raw-event*)))
(assert-event
 (equal (fn-cc-recover-observation *cpa-h-summary* nil 2)
        (list :ok (list *cpa-h-raw-keyring* *cpa-h-raw-event*) 2)))
(make-event
 `(defconst *cpa-h-open*
    ',(fn-sn-open-observed '("fn.letters") 32 2
                           (list *cpa-h-keyring* *cpa-h-event*))))
(assert-event (fn-sn-open-okp *cpa-h-open*))
(defconst *cpa-h-store* (fn-sn-open-state *cpa-h-open*))
(assert-event (equal (fn-cpa-store-auxiliary-agrees *cpa-h-store*) '(:ok 1)))
(assert-event (equal (len (fn-sn-verdicts *cpa-h-store*)) 1))
(assert-event (equal (fn-sn-keyring-snapshots *cpa-h-store*)
                     (list *cpa-h-keyring*)))
