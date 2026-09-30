(in-package "ACL2")
(include-book "../../books/consumer-account-metadata-transition")

; The full relation is a proof oracle here; no served producer calls it.
(defun fn-caammt-seed-hypotheses (history incarnation frontier hn in)
 (declare (xargs :guard t))
 (list (fn-scc-octet-listp history) (equal hn (len history))
       (fn-scc-octet-listp incarnation) (equal in (len incarnation))
       (integerp frontier)))
(defun fn-caammt-seed-correspondp (history incarnation frontier hn in)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (cp metadata) (fn-caac-initial history incarnation frontier hn in)
  (fn-caam-correspondsp cp metadata)))
;@positive fn-caam-initial-establishes-full-metadata
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(1 2) '(3 4) 7 2 2) '(t t t t t))
      (fn-caammt-seed-correspondp '(1 2) '(3 4) 7 2 2)))

;@hypothesis-removal fn-caam-initial-establishes-full-metadata history-octets
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(300) '(3 4) 7 1 2) '(nil t t t t))
      (not (fn-caammt-seed-correspondp '(300) '(3 4) 7 1 2))))

;@hypothesis-removal fn-caam-initial-establishes-full-metadata history-count
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(1 2) '(3 4) 7 3 2) '(t nil t t t))
      (not (fn-caammt-seed-correspondp '(1 2) '(3 4) 7 3 2))))

;@hypothesis-removal fn-caam-initial-establishes-full-metadata incarnation-octets
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(1 2) '(300) 7 2 1) '(t t nil t t))
      (not (fn-caammt-seed-correspondp '(1 2) '(300) 7 2 1))))

;@hypothesis-removal fn-caam-initial-establishes-full-metadata incarnation-count
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(1 2) '(3 4) 7 2 3) '(t t t nil t))
      (not (fn-caammt-seed-correspondp '(1 2) '(3 4) 7 2 3))))

;@hypothesis-removal fn-caam-initial-establishes-full-metadata frontier-scalar
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(1 2) '(3 4) '(7) 2 2) '(t t t t nil))
      (not (fn-caammt-seed-correspondp '(1 2) '(3 4) '(7) 2 2))))

(defconst *caammt-bytes32* (make-list 32 :initial-element 9))
(defconst *caammt-seed* (mv-list 2 (fn-caac-initial *caammt-bytes32* *caammt-bytes32* 0 32 32)))
(defun fn-caammt-event (cp txid op)
 (declare (xargs :guard t))
 (list :consumer-authority (fn-cp-nth 3 cp) txid 0 op))
(defun fn-caammt-run (cp metadata event)
 (declare (xargs :guard t))
 (mv-list 3 (fn-caac-step cp event metadata)))
(defun fn-caammt-cp (result)
 (declare (xargs :guard t))
 (fn-cp-nth 1 (fn-cp-nth 0 result)))
(defun fn-caammt-next (result txid op)
 (declare (xargs :guard t))
 (fn-caammt-run (fn-caammt-cp result) (fn-cp-nth 1 result)
                 (fn-caammt-event (fn-caammt-cp result) txid op)))
(defun fn-caammt-final-op (cp kind)
 (declare (xargs :guard t))
 (let ((p (fn-cp-nth 5 (fn-cp-nth 6 cp))))
  (list kind (fn-cp-nth 1 p) (fn-cp-nth 2 p) (fn-cp-nth 3 p) (fn-cp-nth 7 p))))
(defun fn-caammt-fullp (result)
 (declare (xargs :guard t :verify-guards nil))
 (and (equal (car (car result)) :ok)
      (fn-caam-correspondsp (fn-caammt-cp result) (fn-cp-nth 1 result))))
(defconst *caammt-begin-op* '(:authority-begin (65) 0 1 7))
(defconst *caammt-begin*
 (fn-caammt-run (car *caammt-seed*) (cadr *caammt-seed*)
  (fn-caammt-event (car *caammt-seed*) 1 *caammt-begin-op*)))
(defconst *caammt-row-op*
 (list :authority-row '(65) 0 '(97) 2 *caammt-bytes32*
       (make-list 16 :initial-element 8) *caammt-bytes32*
       *caammt-bytes32* *caammt-bytes32* 1))
(defconst *caammt-row* (fn-caammt-next *caammt-begin* 2 *caammt-row-op*))
(defconst *caammt-seal-op* (fn-caammt-final-op (fn-caammt-cp *caammt-row*) :authority-seal))
(defconst *caammt-seal* (fn-caammt-next *caammt-row* 3 *caammt-seal-op*))
(defconst *caammt-prepare* (fn-caammt-next *caammt-seal* 4 '(:authority-prepare (65) 0)))
(defconst *caammt-fence-op* (fn-caammt-final-op (fn-caammt-cp *caammt-prepare*) :authority-fence))
(defconst *caammt-fence* (fn-caammt-next *caammt-prepare* 5 *caammt-fence-op*))

; Full actual same-pass sequence, including canonical carry of the completed
; publication root. Pending stages do not produce an authorizing root.
;@mutation-witness fn-caam-full-stage-fence-lifecycle
(assert-event
 (and (fn-caam-correspondsp (car *caammt-seed*) (cadr *caammt-seed*))
      (fn-caammt-fullp *caammt-begin*) (fn-caammt-fullp *caammt-row*)
      (fn-caammt-fullp *caammt-seal*) (fn-caammt-fullp *caammt-prepare*)
      (fn-caammt-fullp *caammt-fence*)
      (null (fn-cp-nth 2 (car *caammt-begin*)))
      (null (fn-cp-nth 2 (car *caammt-row*)))
      (null (fn-cp-nth 2 (car *caammt-seal*)))
      (null (fn-cp-nth 2 (car *caammt-prepare*)))
      (consp (fn-cp-nth 2 (car *caammt-fence*)))
      (equal (fn-cp-nth 2 *caammt-fence*)
             (fn-scs-summary (fn-cp-nth 2 (car *caammt-fence*))))))

(defun fn-caammt-stage-hypotheses (s event row credential old-rest advanced metadata)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p)))
  (list (fn-caam-authority-sizep a) (consp p)
        (equal metadata (fn-caam-annotation s))
        (fn-cais-triep (fn-cp-nth 2 (fn-cp-nth 5 prep)))
        (fn-scc-octet-listp (fn-cp-nth 1 row))
        (equal old-rest (if advanced (cdr (fn-cp-nth 2 prep)) (fn-cp-nth 2 prep)))
        (equal (fn-caac-row-carry row) (fn-scs-summary row))
        (implies credential (equal (fn-caac-credential-carry (fn-cp-nth 4 event))
                                   (fn-scs-summary credential))))))
(defun fn-caammt-stage-correspondp (s event row credential old-rest advanced metadata)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (one new-metadata)
  (fn-caac-stage-selected s (fn-cp-nth 6 s) event row credential old-rest advanced metadata)
  (fn-caam-correspondsp (fn-cp-nth 1 one) new-metadata)))
(defconst *caammt-row-event*
 (fn-caammt-event (fn-caammt-cp *caammt-begin*) 2 *caammt-row-op*))
(defconst *caammt-plan*
 (fn-caa-row-plan (fn-cp-nth 6 (fn-caammt-cp *caammt-begin*)) *caammt-row-event* *caammt-row-op*))
;@positive fn-caam-selected-stage-maintains-full-metadata
(assert-event
 (let ((s (fn-caammt-cp *caammt-begin*)) (row (fn-cp-nth 1 *caammt-plan*))
       (credential (fn-cp-nth 2 *caammt-plan*)) (old-rest (fn-cp-nth 3 *caammt-plan*))
       (advanced (fn-cp-nth 4 *caammt-plan*)) (metadata (fn-cp-nth 1 *caammt-begin*)))
  (and (equal (car *caammt-plan*) :stage)
       (equal (fn-caammt-stage-hypotheses s *caammt-row-event* row credential old-rest advanced metadata)
              '(t t t t t t t t))
       (fn-caammt-stage-correspondp s *caammt-row-event* row credential old-rest advanced metadata))))

; Explicit corrupted-state/selected-input witness; all other literal premises hold.
;@hypothesis-removal fn-caam-selected-stage-maintains-full-metadata authority-size-domain
(assert-event
 (let* ((original (fn-caammt-cp *caammt-begin*))
         (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
         (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
         (original-row (fn-cp-nth 1 *caammt-plan*))
         (original-credential (fn-cp-nth 2 *caammt-plan*))
         (s (update-nth 6 (update-nth 5 (update-nth 5 (update-nth 5 (update-nth 1 '(bad) root) prep) p) a) original))
         (row original-row) (credential original-credential) (old-rest nil) (advanced nil)
         (metadata (fn-caam-annotation s)))
  (declare (ignorable a p prep root original-row original-credential))
  (and (equal (fn-caammt-stage-hypotheses s *caammt-row-event* row credential old-rest advanced metadata)
              '(nil t t t t t t t))
       (not (fn-caammt-stage-correspondp s *caammt-row-event* row credential old-rest advanced metadata)))))

; Explicit corrupted-state/selected-input witness; all other literal premises hold.
;@hypothesis-removal fn-caam-selected-stage-maintains-full-metadata pending-present
(assert-event
 (let* ((original (fn-caammt-cp *caammt-begin*))
         (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
         (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
         (original-row (fn-cp-nth 1 *caammt-plan*))
         (original-credential (fn-cp-nth 2 *caammt-plan*))
         (s (update-nth 6 (update-nth 5 nil a) original))
         (row original-row) (credential original-credential) (old-rest nil) (advanced nil)
         (metadata (fn-caam-annotation s)))
  (declare (ignorable a p prep root original-row original-credential))
  (and (equal (fn-caammt-stage-hypotheses s *caammt-row-event* row credential old-rest advanced metadata)
              '(t nil t t t t t t))
       (not (fn-caammt-stage-correspondp s *caammt-row-event* row credential old-rest advanced metadata)))))

; Explicit corrupted-state/selected-input witness; all other literal premises hold.
;@hypothesis-removal fn-caam-selected-stage-maintains-full-metadata old-complete-metadata
(assert-event
 (let* ((original (fn-caammt-cp *caammt-begin*))
         (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
         (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
         (original-row (fn-cp-nth 1 *caammt-plan*))
         (original-credential (fn-cp-nth 2 *caammt-plan*))
         (s original) (row original-row) (credential original-credential)
         (old-rest nil) (advanced nil) (metadata (update-nth 1 nil (fn-caam-annotation s))))
  (declare (ignorable a p prep root original-row original-credential))
  (and (equal (fn-caammt-stage-hypotheses s *caammt-row-event* row credential old-rest advanced metadata)
              '(t t nil t t t t t))
       (not (fn-caammt-stage-correspondp s *caammt-row-event* row credential old-rest advanced metadata)))))

; Explicit corrupted-state/selected-input witness; all other literal premises hold.
;@hypothesis-removal fn-caam-selected-stage-maintains-full-metadata maintained-trie
(assert-event
 (let* ((original (fn-caammt-cp *caammt-begin*))
         (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
         (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
         (original-row (fn-cp-nth 1 *caammt-plan*))
         (original-credential (fn-cp-nth 2 *caammt-plan*))
         (s (update-nth 6 (update-nth 5 (update-nth 5 (update-nth 5
                (update-nth 2 (list (cons '(bad) nil)) root) prep) p) a) original))
         (row original-row) (credential original-credential) (old-rest nil) (advanced nil)
         (metadata (fn-caam-annotation s)))
  (declare (ignorable a p prep root original-row original-credential))
  (and (equal (fn-caammt-stage-hypotheses s *caammt-row-event* row credential old-rest advanced metadata)
              '(t t t nil t t t t))
       (not (fn-caammt-stage-correspondp s *caammt-row-event* row credential old-rest advanced metadata)))))

; Explicit corrupted-state/selected-input witness; all other literal premises hold.
;@hypothesis-removal fn-caam-selected-stage-maintains-full-metadata row-name-octets
(assert-event
 (let* ((original (fn-caammt-cp *caammt-begin*))
         (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
         (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
         (original-row (fn-cp-nth 1 *caammt-plan*))
         (original-credential (fn-cp-nth 2 *caammt-plan*))
         (s original)
         (row (update-nth 2 (take 46 (fn-cp-nth 2 original-row)) (update-nth 1 '(256) original-row)))
         (credential original-credential) (old-rest nil) (advanced nil)
         (metadata (fn-caam-annotation s)))
  (declare (ignorable a p prep root original-row original-credential))
  (and (equal (fn-caammt-stage-hypotheses s *caammt-row-event* row credential old-rest advanced metadata)
              '(t t t t nil t t t))
       (not (fn-caammt-stage-correspondp s *caammt-row-event* row credential old-rest advanced metadata)))))

; Explicit corrupted-state/selected-input witness; all other literal premises hold.
;@hypothesis-removal fn-caam-selected-stage-maintains-full-metadata old-cursor-step
(assert-event
 (let* ((original (fn-caammt-cp *caammt-begin*))
         (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
         (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
         (original-row (fn-cp-nth 1 *caammt-plan*))
         (original-credential (fn-cp-nth 2 *caammt-plan*))
         (s original) (row original-row) (credential original-credential)
         (old-rest '(bad)) (advanced nil) (metadata (fn-caam-annotation s)))
  (declare (ignorable a p prep root original-row original-credential))
  (and (equal (fn-caammt-stage-hypotheses s *caammt-row-event* row credential old-rest advanced metadata)
              '(t t t t t nil t t))
       (not (fn-caammt-stage-correspondp s *caammt-row-event* row credential old-rest advanced metadata)))))

; Explicit corrupted-state/selected-input witness; all other literal premises hold.
;@hypothesis-removal fn-caam-selected-stage-maintains-full-metadata selected-row-carry
(assert-event
 (let* ((original (fn-caammt-cp *caammt-begin*))
         (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
         (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
         (original-row (fn-cp-nth 1 *caammt-plan*))
         (original-credential (fn-cp-nth 2 *caammt-plan*))
         (s original) (row (update-nth 2 (take 47 (fn-cp-nth 2 original-row)) original-row))
         (credential original-credential) (old-rest nil) (advanced nil)
         (metadata (fn-caam-annotation s)))
  (declare (ignorable a p prep root original-row original-credential))
  (and (equal (fn-caammt-stage-hypotheses s *caammt-row-event* row credential old-rest advanced metadata)
              '(t t t t t t nil t))
       (not (fn-caammt-stage-correspondp s *caammt-row-event* row credential old-rest advanced metadata)))))

; Explicit corrupted-state/selected-input witness; all other literal premises hold.
;@hypothesis-removal fn-caam-selected-stage-maintains-full-metadata selected-credential-carry
(assert-event
 (let* ((original (fn-caammt-cp *caammt-begin*))
         (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
         (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
         (original-row (fn-cp-nth 1 *caammt-plan*))
         (original-credential (fn-cp-nth 2 *caammt-plan*))
         (s original) (row original-row) (credential '(bad))
         (old-rest nil) (advanced nil) (metadata (fn-caam-annotation s)))
  (declare (ignorable a p prep root original-row original-credential))
  (and (equal (fn-caammt-stage-hypotheses s *caammt-row-event* row credential old-rest advanced metadata)
              '(t t t t t t t nil))
       (not (fn-caammt-stage-correspondp s *caammt-row-event* row credential old-rest advanced metadata)))))
