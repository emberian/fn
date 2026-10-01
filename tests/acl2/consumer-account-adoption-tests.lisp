(in-package "ACL2")
(include-book "../../books/consumer-account-adoption")

(defconst *caat-32* (make-list 32 :initial-element 9))
(defconst *caat-16* (make-list 16 :initial-element 8))
(defconst *caat-initial* (fn-cp-state *caat-32* *caat-32* 0 1 nil))

(defun fn-caat-event (s txid op)
  (list :consumer-authority (fn-cp-nth 3 s) txid 0 op))
(defun fn-caat-row-op (candidate base login birth digest)
  (list :authority-row candidate base login birth *caat-32* *caat-16*
        digest *caat-32* *caat-32* 1))
(defun fn-caat-next (s txid op)
  (fn-cp-nth 1 (fn-caa-step s (fn-caat-event s txid op))))
(defun fn-caat-seal (s txid)
  (let ((p (fn-cp-nth 5 (fn-cp-nth 6 s))))
    (fn-caat-next s txid (list :authority-seal (fn-cp-nth 1 p)
                               (fn-cp-nth 2 p) (fn-cp-nth 3 p) (fn-cp-nth 7 p)))))
(defun fn-caat-fence (s txid)
  (let ((p (fn-cp-nth 5 (fn-cp-nth 6 s))))
    (fn-caa-step s (fn-caat-event s txid
                   (list :authority-fence (fn-cp-nth 1 p) (fn-cp-nth 2 p)
                         (fn-cp-nth 3 p) (fn-cp-nth 7 p))))))

(defconst *caat-begin-event*
  (fn-caat-event *caat-initial* 1 '(:authority-begin (65) 0 1 7)))
(defconst *caat-begun* (fn-cp-nth 1 (fn-caa-step *caat-initial* *caat-begin-event*)))
(defconst *caat-row-event*
  (fn-caat-event *caat-begun* 2 (fn-caat-row-op '(65) 0 '(97) 2 *caat-32*)))
(defconst *caat-staged* (fn-cp-nth 1 (fn-caa-step *caat-begun* *caat-row-event*)))
(defconst *caat-sealed* (fn-caat-seal *caat-staged* 3))
(defconst *caat-ready* (fn-caat-next *caat-sealed* 4 '(:authority-prepare (65) 0)))
(defconst *caat-committed* (fn-caat-fence *caat-ready* 5))
(defconst *caat-first* (fn-cp-nth 1 *caat-committed*))
(defconst *caat-root* (fn-cp-nth 2 *caat-committed*))
(defconst *caat-token* (fn-cp-nth 2 (car (fn-cp-nth 4 (fn-cp-nth 6 *caat-first*)))))

; Reachable source path, not a host persistence witness. Every stage retains
; old authority; only the exact fence returns the complete index/auth root.
;@positive fn-caa-stages-preserve-current-authority
(assert-event
 (and (fn-cp-statep *caat-initial*) (fn-cp-statep *caat-begun*)
      (fn-cp-statep *caat-staged*) (fn-cp-statep *caat-sealed*)
      (fn-cp-statep *caat-ready*) (fn-cp-statep *caat-first*)
      (eq (car (fn-caa-step *caat-begun* *caat-row-event*)) :ok)
      (not (eq (fn-cp-nth 0 (fn-cp-nth 4 *caat-row-event*)) :authority-fence))
      (equal (fn-cp-nth 1 (fn-cp-nth 6 *caat-staged*)) 0)
      (equal (fn-cp-nth 2 (fn-cp-nth 6 *caat-staged*)) 1)
      (null (fn-cp-nth 3 (fn-cp-nth 6 *caat-staged*)))
      (null (fn-cp-nth 4 (fn-cp-nth 6 *caat-staged*)))
      (null (fn-cp-nth 2 (fn-caa-step *caat-begun* *caat-row-event*)))
      (null (fn-cp-authority-find '(97) (fn-cp-nth 4 (fn-cp-nth 6 *caat-staged*))))
      (fn-auth-configp (fn-caa-root-auth-config *caat-root*))
      (equal (fn-cp-nth 1 (fn-cp-nth 6 *caat-first*)) 1)
      (equal (fn-cp-creation-coordinate *caat-token*) 2)
      (equal (len *caat-token*) 48)
      (equal (fn-cp-nth 2 (fn-cp-nth 1 (fn-caa-current-binding '(97) *caat-root*)))
             *caat-token*)))

;@positive fn-caa-account-creation-is-48-octets
;@positive fn-caa-account-creation-records-stage-coordinate
(assert-event
 (let ((namespace (fn-cp-nth 3 (fn-cp-nth 6 *caat-first*))))
   (and (fn-cp-authority-namespacep namespace) (fn-cp-uintp 2)
        (fn-cbor-octet-listp (fn-cp-account-creation namespace 2))
        (equal (len (fn-cp-account-creation namespace 2)) 48)
        (equal (fn-cp-creation-coordinate (fn-cp-account-creation namespace 2)) 2))))

;@hypothesis-removal fn-caa-stages-preserve-current-authority nonfence
(assert-event
 (let* ((p (fn-cp-nth 5 (fn-cp-nth 6 *caat-ready*)))
        (e (fn-caat-event *caat-ready* 5
             (list :authority-fence '(65) 0 (fn-cp-nth 3 p) (fn-cp-nth 7 p))))
        (one (fn-caa-step *caat-ready* e)))
   (and (eq (car one) :ok)
        (eq (fn-cp-nth 0 (fn-cp-nth 4 e)) :authority-fence)
        (not (equal (fn-cp-nth 4 (fn-cp-nth 6 (fn-cp-nth 1 one)))
                    (fn-cp-nth 4 (fn-cp-nth 6 *caat-ready*)))))))

; Premature, wrong-count, wrong-digest and stale-base fences cannot publish.
(assert-event
 (let* ((p (fn-cp-nth 5 (fn-cp-nth 6 *caat-staged*)))
        (early (fn-caat-fence *caat-staged* 3)))
   (and (not (eq (car early) :ok))
        (not (eq (car (fn-caa-step *caat-ready*
                        (fn-caat-event *caat-ready* 5
                          (list :authority-fence '(65) 0 2 (fn-cp-nth 7 p))))) :ok))
        (not (eq (car (fn-caa-step *caat-ready*
                        (fn-caat-event *caat-ready* 5
                          (list :authority-fence '(65) 0 1 (make-list 32 :initial-element 0))))) :ok))
        (not (eq (car (fn-caa-step *caat-ready*
                        (fn-caat-event *caat-ready* 5
                          (list :authority-fence '(65) 1 1 (fn-cp-nth 7 p))))) :ok)))))

; Row birth must name the actual persisted stage coordinate. Reservation
; expectations/provisional values cannot authorize an incorrect incarnation.
(assert-event
 (and (not (eq (car (fn-caa-step *caat-begun*
                      (fn-caat-event *caat-begun* 2
                        (fn-caat-row-op '(65) 0 '(97) 3 *caat-32*)))) :ok))
      (not (eq (car (fn-caa-step *caat-begun*
                      (fn-caat-event *caat-begun* 4294967296
                        (fn-caat-row-op '(65) 0 '(97) 4294967296 *caat-32*)))) :ok))))

; Credential rotation preserves the adopted token and bumps the view at
; fence. Committed deletion retains a tombstone; recreation gets fresh birth.
(defconst *caat-second-begin*
  (fn-caat-next *caat-first* 6 '(:authority-begin (66) 1 3 7)))
(defconst *caat-rotated*
  (fn-caat-next *caat-second-begin* 7
    (fn-caat-row-op '(66) 1 '(97) 2 (make-list 32 :initial-element 10))))
(defconst *caat-second-ready*
  (fn-caat-next (fn-caat-seal *caat-rotated* 8) 9 '(:authority-prepare (66) 1)))
(defconst *caat-second* (fn-cp-nth 1 (fn-caat-fence *caat-second-ready* 10)))
(defconst *caat-delete-begin*
  (fn-caat-next *caat-second* 11 '(:authority-begin (67) 2 8 7)))
(defconst *caat-deleted-staged*
  (fn-caat-next *caat-delete-begin* 12 '(:authority-tombstone (67) 2 (97) 2)))
(defconst *caat-delete-ready*
  (fn-caat-next (fn-caat-seal *caat-deleted-staged* 13) 14 '(:authority-prepare (67) 2)))
(defconst *caat-deleted-result* (fn-caat-fence *caat-delete-ready* 15))
(defconst *caat-deleted* (fn-cp-nth 1 *caat-deleted-result*))
(defconst *caat-recreate-begin*
  (fn-caat-next *caat-deleted* 16 '(:authority-begin (68) 3 13 7)))
(defconst *caat-recreated-staged*
  (fn-caat-next *caat-recreate-begin* 17 (fn-caat-row-op '(68) 3 '(97) 17 *caat-32*)))
(defconst *caat-recreate-ready*
  (fn-caat-next (fn-caat-seal *caat-recreated-staged* 18) 19 '(:authority-prepare (68) 3)))
(defconst *caat-recreated* (fn-cp-nth 1 (fn-caat-fence *caat-recreate-ready* 20)))

(assert-event
 (let ((rotated-row (car (fn-cp-nth 4 (fn-cp-nth 6 *caat-second*))))
       (deleted-row (car (fn-cp-nth 4 (fn-cp-nth 6 *caat-deleted*))))
       (recreated-row (car (fn-cp-nth 4 (fn-cp-nth 6 *caat-recreated*)))))
   (and (fn-cp-statep *caat-second*) (fn-cp-statep *caat-deleted*)
        (fn-cp-statep *caat-recreated*)
        (equal (fn-cp-nth 2 rotated-row) *caat-token*)
        (equal (fn-cp-nth 2 deleted-row) *caat-token*)
        (not (fn-cp-nth 3 deleted-row)) (null (fn-cp-nth 4 deleted-row))
        (null (fn-caa-current-binding '(97) (fn-cp-nth 2 *caat-deleted-result*)))
        (not (equal (fn-cp-nth 2 recreated-row) *caat-token*))
        (equal (fn-cp-creation-coordinate (fn-cp-nth 2 recreated-row)) 17)
        (equal (fn-cp-nth 1 (fn-cp-nth 6 *caat-recreated*)) 4))))

; A table cannot seal while an old account is omitted without a tombstone.
(assert-event
 (and (fn-cp-statep *caat-second-begin*)
      (not (eq (car (fn-caa-step *caat-second-begin*
        (fn-caat-event *caat-second-begin* 7
          (list :authority-seal '(66) 1 0
                (fn-cp-nth 7 (fn-cp-nth 5 (fn-cp-nth 6 *caat-second-begin*))))))) :ok))))

; Restart at each preparation cut uses the same literal durable interpreter;
; changing/dropping a coordinate refuses rather than silently renumbering.
(assert-event
 (let* ((seal-event (fn-caat-event *caat-staged* 3
          (let ((p (fn-cp-nth 5 (fn-cp-nth 6 *caat-staged*))))
            (list :authority-seal '(65) 0 1 (fn-cp-nth 7 p)))))
        (prepare-event (fn-caat-event *caat-sealed* 4 '(:authority-prepare (65) 0)))
        (fence-event (fn-caat-event *caat-ready* 5
          (let ((p (fn-cp-nth 5 (fn-cp-nth 6 *caat-ready*))))
            (list :authority-fence '(65) 0 1 (fn-cp-nth 7 p))))))
   (and (equal (fn-caa-replay *caat-initial* nil
                  (list *caat-begin-event* *caat-row-event* seal-event prepare-event fence-event))
               *caat-committed*)
        (equal (fn-caa-replay *caat-staged* nil (list seal-event prepare-event fence-event))
               *caat-committed*)
        (not (eq (car (fn-caa-replay *caat-begun* nil (list seal-event))) :ok)))))

;@hypothesis-removal fn-caa-stages-preserve-current-authority success
(assert-event
 (let* ((e (fn-caat-event *caat-begun* 2
             (fn-caat-row-op '(65) 0 '(97) 3 *caat-32*)))
        (one (fn-caa-step *caat-begun* e)))
   (and (not (eq (car one) :ok))
        (not (eq (fn-cp-nth 0 (fn-cp-nth 4 e)) :authority-fence))
        (not (equal (fn-cp-nth 2 (fn-cp-nth 6 (fn-cp-nth 1 one)))
                    (fn-cp-nth 2 (fn-cp-nth 6 *caat-begun*)))))))

; Corrupted-constructor logical witnesses intentionally evaluate the total
; model outside the u64 decoder execution domain; valid path tests retain
; ordinary guard checking. These are not native malformed-state witnesses.
;@hypothesis-removal fn-caa-account-creation-is-48-octets namespace
;@hypothesis-removal fn-caa-account-creation-records-stage-coordinate namespace
(assert-event
 (with-guard-checking :none
 (let ((bad (make-list 39 :initial-element 9)))
   (and (not (fn-cp-authority-namespacep bad)) (fn-cp-uintp 2)
        (not (equal (len (fn-cp-account-creation bad 2)) 48))
        (not (equal (fn-cp-creation-coordinate (fn-cp-account-creation bad 2)) 2))))))

;@hypothesis-removal fn-caa-account-creation-is-48-octets txid
;@hypothesis-removal fn-caa-account-creation-records-stage-coordinate txid
(assert-event
 (with-guard-checking :none
 (let ((namespace (fn-cp-nth 3 (fn-cp-nth 6 *caat-first*))))
   (and (fn-cp-authority-namespacep namespace) (not (fn-cp-uintp 4294967296))
        (not (equal (len (fn-cp-account-creation namespace 4294967296)) 48))
        (not (equal (fn-cp-creation-coordinate
                       (fn-cp-account-creation namespace 4294967296)) 4294967296))))))

; A two-account table exercises multiple name paths and durable reversal
; cuts. One tick cannot mark the whole candidate ready or authorize a fence.
(defconst *caat-two-rows*
  (fn-caat-next *caat-staged* 3 (fn-caat-row-op '(65) 0 '(98) 3 *caat-32*)))
(defconst *caat-two-sealed* (fn-caat-seal *caat-two-rows* 4))
(defconst *caat-two-partial*
  (fn-caat-next *caat-two-sealed* 5 '(:authority-prepare (65) 0)))
(defconst *caat-two-ready*
  (fn-caat-next *caat-two-partial* 6 '(:authority-prepare (65) 0)))
(defconst *caat-two-result* (fn-caat-fence *caat-two-ready* 7))
(defconst *caat-two* (fn-cp-nth 1 *caat-two-result*))
(assert-event
 (let ((rows (fn-cp-nth 4 (fn-cp-nth 6 *caat-two*)))
       (root (fn-cp-nth 2 *caat-two-result*)))
   (and (fn-cp-statep *caat-two-rows*) (fn-cp-statep *caat-two-partial*)
        (not (eq (car (fn-caat-fence *caat-two-partial* 6)) :ok))
        (fn-cp-statep *caat-two*) (equal (len rows) 2)
        (equal (fn-cp-nth 1 (car rows)) '(97))
        (equal (fn-cp-nth 1 (cadr rows)) '(98))
        (equal (fn-cp-nth 1 (fn-caa-current-binding '(97) root)) (car rows))
        (equal (fn-cp-nth 1 (fn-caa-current-binding '(98) root)) (cadr rows))
        (equal (len (fn-auth-config-creds (fn-caa-root-auth-config root))) 2)
        (fn-auth-configp (fn-caa-root-auth-config root))
        (not (eq (car (fn-caa-step *caat-two-rows*
                        (fn-caat-event *caat-two-rows* 4
                          (fn-caat-row-op '(65) 0 '(97) 4 *caat-32*)))) :ok)))))

; Complete old/new merge: deleting A must occur before retaining B and
; adding C. The old A token survives in its tombstone, B's stays literal,
; and C names its exact persisted stage coordinate.
(defconst *caat-merge-begin*
  (fn-caat-next *caat-two* 8 '(:authority-begin (69) 1 4 7)))
(defconst *caat-merge-delete*
  (fn-caat-next *caat-merge-begin* 9 '(:authority-tombstone (69) 1 (97) 2)))
(defconst *caat-merge-retain*
  (fn-caat-next *caat-merge-delete* 10 (fn-caat-row-op '(69) 1 '(98) 3 *caat-32*)))
(defconst *caat-merge-new*
  (fn-caat-next *caat-merge-retain* 11 (fn-caat-row-op '(69) 1 '(99) 11 *caat-32*)))
(defconst *caat-merge-ready*
  (fn-caat-next
   (fn-caat-next
    (fn-caat-next (fn-caat-seal *caat-merge-new* 12) 13 '(:authority-prepare (69) 1))
    14 '(:authority-prepare (69) 1))
   15 '(:authority-prepare (69) 1)))
(defconst *caat-merge-result* (fn-caat-fence *caat-merge-ready* 16))
(assert-event
 (let* ((s (fn-cp-nth 1 *caat-merge-result*))
        (rows (fn-cp-nth 4 (fn-cp-nth 6 s)))
        (old (fn-cp-nth 4 (fn-cp-nth 6 *caat-two*)))
        (root (fn-cp-nth 2 *caat-merge-result*)))
   (and (not (eq (car (fn-caa-step *caat-merge-begin*
                        (fn-caat-event *caat-merge-begin* 9
                          (fn-caat-row-op '(69) 1 '(98) 3 *caat-32*)))) :ok))
        (fn-cp-statep s) (equal (len rows) 3)
        (equal (fn-cp-nth 2 (car rows)) (fn-cp-nth 2 (car old)))
        (equal (fn-cp-nth 2 (cadr rows)) (fn-cp-nth 2 (cadr old)))
        (equal (fn-cp-creation-coordinate (fn-cp-nth 2 (caddr rows))) 11)
        (null (fn-caa-current-binding '(97) root))
        (fn-caa-current-binding '(98) root) (fn-caa-current-binding '(99) root)
        (fn-auth-configp (fn-caa-root-auth-config root))
        (equal (len (fn-auth-config-creds (fn-caa-root-auth-config root))) 2))))
