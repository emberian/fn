(in-package "ACL2")
(include-book "../../books/checkpoint-auxiliary")
(include-book "../../books/store-observed")
(include-book "../../books/hybrid-store")
(include-book "../../books/codec-attach")

; The clone caller bounds both raw CLI paths and canonical/derived paths by
; the same ACL2-owned native Store path width before filesystem traversal.
(assert-event (equal (fn-cpa-clone-path-bound) *fn-ncfg-max-path*))
(assert-event
 (fn-cpa-clone-input-pathp (cons 47 (make-list 511 :initial-element 97))))
(assert-event
 (not (fn-cpa-clone-input-pathp
       (cons 47 (make-list 512 :initial-element 97)))))
(assert-event (not (fn-cpa-clone-input-pathp '(97 98 99))))
(assert-event (not (fn-cpa-clone-input-pathp '(47 97 0 98))))

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
                     '(:ok 2)))
(assert-event (equal (fn-cp-nth 2 (fn-sn-consumer *cpa-reopened*))
                     '(110 101 119)))
(assert-event (equal (fn-cp-nth 3 (fn-sn-consumer *cpa-reopened*)) 5))
(assert-event (equal (fn-sn-identity-next *cpa-reopened*) 5))
(assert-event (equal (fn-sn-keyring-snapshots *cpa-reopened*)
                     (list *cpa-snapshot*)))
(assert-event (equal (fn-sn-verdicts *cpa-reopened*) nil))

; A selected exact-prefix pack also retains an acknowledged E2 cursor.  The
; writable clone rollover fences that cursor by changing incarnation, while
; the original registration and progress remain in the recovered history.
(defconst *cpa-progress-boot* (fn-cpe-make 0 0 0 '(:bootstrap (1) (2))))
(defconst *cpa-progress-register*
  (fn-cpe-make 1 1 1 '(:register (3) (4) (5) 1 1 1)))
(defconst *cpa-progress-cursor*
  (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 2))
(defconst *cpa-progress-ack*
  (fn-cpe-make 2 2 2 (list :ack *cpa-progress-cursor*)))
(defconst *cpa-progress-rollover*
  (fn-cpe-make 3 3 3 '(:rollover (6))))
(make-event `(defconst *cpa-progress-raw-boot*
               ',(fn-store-event-encode *cpa-progress-boot*)))
(make-event `(defconst *cpa-progress-raw-register*
               ',(fn-store-event-encode *cpa-progress-register*)))
(make-event `(defconst *cpa-progress-raw-ack*
               ',(fn-store-event-encode *cpa-progress-ack*)))
(make-event `(defconst *cpa-progress-raw-rollover*
               ',(fn-store-event-encode *cpa-progress-rollover*)))
(defconst *cpa-progress-pack*
  (fn-cc-make 3 3 (list *cpa-progress-raw-boot*
                        *cpa-progress-raw-register*
                        *cpa-progress-raw-ack*)))
(assert-event
 (equal (fn-cc-recover-observation
         *cpa-progress-pack*
         (list (list 3 *cpa-progress-raw-rollover*)) 4)
        (list :ok (list *cpa-progress-raw-boot*
                        *cpa-progress-raw-register*
                        *cpa-progress-raw-ack*
                        *cpa-progress-raw-rollover*) 4)))
(make-event
 `(defconst *cpa-progress-before-rollover*
    ',(fn-sn-open-observed
       '("g") 32 3
       (list *cpa-progress-boot* *cpa-progress-register*
             *cpa-progress-ack*))))
(assert-event (fn-sn-open-okp *cpa-progress-before-rollover*))
(assert-event
 (equal (nth 7
             (fn-cp-find '(3)
                         (nth 5 (fn-sn-consumer
                                 (fn-sn-open-state
                                  *cpa-progress-before-rollover*)))))
        2))
(make-event
 `(defconst *cpa-progress-after-rollover*
    ',(fn-sn-open-observed
       '("g") 32 4
       (list *cpa-progress-boot* *cpa-progress-register*
             *cpa-progress-ack* *cpa-progress-rollover*))))
(assert-event (fn-sn-open-okp *cpa-progress-after-rollover*))
(assert-event
 (equal (fn-cpa-clone-phase
         (fn-sn-open-state *cpa-progress-after-rollover*)
         *cpa-progress-rollover*)
        :completed))
(assert-event
 (equal (nth 5 (fn-sn-consumer
                (fn-sn-open-state *cpa-progress-after-rollover*)))
        nil))
(assert-event
 (equal (fn-cpa-store-auxiliary-agrees
         (fn-sn-open-state *cpa-progress-after-rollover*))
        '(:ok 2)))
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
(assert-event
 (equal (fn-cpa-rollover-proposal *cpa-reopened* '(110 101 119))
        '(:refused :same-incarnation)))
(assert-event
 (equal (fn-cpa-rollover-proposal *cpa-reopened* '(104 105 115 116))
        '(:refused :history-id)))
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
(assert-event (equal (fn-cpa-store-auxiliary-agrees *cpa-h-store*) '(:ok 2)))
(assert-event (equal (len (fn-sn-verdicts *cpa-h-store*)) 1))
(assert-event (equal (fn-sn-keyring-snapshots *cpa-h-store*)
                     (list *cpa-h-keyring*)))
; The historical topic projection carries the accepted source and snapshot
; even before any topic anchor.  A node-only checkpoint would miss both.
(assert-event (equal (fn-th-at 0 (fn-sn-topic *cpa-h-store*)) :ok))
(assert-event (consp (fn-th-at 3 (fn-sn-topic *cpa-h-store*))))
(assert-event
 (equal (fn-cpa-store-auxiliary-agrees
         (fn-sn-with-topic *cpa-h-store* nil))
        '(:mismatch :auxiliary-state)))
; A derived index is rebuilt from exact dense Store positions; replacing the
; maintained value without changing the journal is a mismatch too.
(assert-event (consp (fn-sn-event-index *cpa-h-store*)))
(assert-event
 (equal (fn-cpa-store-auxiliary-agrees
         (fn-sn-with-event-index *cpa-h-store* nil))
        '(:mismatch :auxiliary-state)))
