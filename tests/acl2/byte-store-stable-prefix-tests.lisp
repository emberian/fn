; K5 teeth use the actual frontier and record programs with concrete codecs.
(in-package "ACL2")
(include-book "../../books/byte-store-stable-prefix")
(include-book "../../books/byte-store-relation")
(include-book "../../books/byte-store-programs")
(include-book "../../books/byte-store-frame")
(include-book "../../books/byte-store-txn-name")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bsk5-groups* '("fn.letters" "fn.test"))
(defconst *bsk5-capacity* 10)
(defconst *bsk5-record*
  (fn-record-make 0 0 0 "<k5@example.invalid>" '(65)
                  '("fn.letters") "archive" "subject" "evidence" 1 841000000))

;; The records flip: the kernel stages RETAINED rows (a held row whose payload
;; is an arena handle); the frame on disk is the WIRE record, alpha of the
;; row through the arena.  *bsk5-arena* is the arena's logical value (the
;; sealed payloads, handle 0 and handle 1); the rows are what the intern
;; makes for the two wire records (fn-held-plain: the context the intern
;; computes under no keyring, verdict :absent at generation 0).
(defconst *bsk5-arena*
  (list (fn-record-payload *bsk5-record*) '(66)))
(defconst *bsk5-row* (fn-held-plain *bsk5-record* 0))

(defun bsk5-frame ()
  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                 *fn-frame-store-kind* (fn-store-event-encode *bsk5-record*)))
(defun bsk5-initial ()
  (fn-bs-initial-image 4 (fn-bs-initial-config-octets)
                       (fn-bs-initial-frontier-octets)))
(defun bsk5-frontier-run ()
  (fn-bs-run (bsk5-initial) (fn-sf-initial-state)
             (fn-bs-frontier-program ".allocation-k5" (fn-bs-frontier-encode 1))
             nil *bsk5-groups* *bsk5-capacity*))
(defun bsk5-record-run ()
  (let* ((pair (car (last (bsk5-frontier-run))))
         (prepared (fn-sf-prepare-record (cdr pair) *bsk5-row*
                                         *bsk5-groups* *bsk5-capacity*)))
    (fn-bs-run (car pair) prepared
               (fn-bs-record-program ".stage-k5" (fn-bs-txn-name 0)
                                     (bsk5-frame))
               nil *bsk5-groups* *bsk5-capacity*)))
(defun bsk5-linked () (nth 8 (bsk5-record-run)))
(defconst *bsk5-record-2*
  (fn-record-make 1 1 1 "<k5-second@example.invalid>" '(66)
                  '("fn.letters") "archive-2" "subject-2" "evidence-2" 1 841000001))
(defconst *bsk5-row-2* (fn-held-plain *bsk5-record-2* 1))

; Alpha of each row through the arena is its wire record (non-vacuity of the
; relation's record arms: the kernel's rows and the decoded frames meet).
(assert-event
 (and (fn-held-p *bsk5-row*) (fn-held-p *bsk5-row-2*)
      (fn-store-event-p *bsk5-row*) (not (fn-record-p *bsk5-row*))
      (equal (fn-bs-row-wire *bsk5-row* *bsk5-arena*) *bsk5-record*)
      (equal (fn-bs-row-wire *bsk5-row-2* *bsk5-arena*) *bsk5-record-2*)
      (fn-record-p (fn-bs-row-wire *bsk5-row-2* *bsk5-arena*))
      (equal (fn-bs-rows-wire (list *bsk5-row* *bsk5-row-2*) *bsk5-arena*)
             (list *bsk5-record* *bsk5-record-2*))))
(defun bsk5-frame-2 ()
  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                 *fn-frame-store-kind* (fn-store-event-encode *bsk5-record-2*)))
(defun bsk5-finished ()
  (let ((pair (car (last (bsk5-record-run)))))
    (car (last (fn-bs-run (car pair) (cdr pair)
                           (fn-bs-finish-program 0 0)
                           nil *bsk5-groups* *bsk5-capacity*)))))
(defun bsk5-frontier-2 ()
  (let ((pair (bsk5-finished)))
    (car (last (fn-bs-run (car pair) (cdr pair)
                           (fn-bs-frontier-program ".allocation-k5-2"
                                                   (fn-bs-frontier-encode 2))
                           nil *bsk5-groups* *bsk5-capacity*)))))
(defun bsk5-record-2-run ()
  (let* ((pair (bsk5-frontier-2))
         (prepared (fn-sf-prepare-record (cdr pair) *bsk5-row-2*
                                         *bsk5-groups* *bsk5-capacity*)))
    (fn-bs-run (car pair) prepared
               (fn-bs-record-program ".stage-k5-2" (fn-bs-txn-name 1)
                                     (bsk5-frame-2))
               nil *bsk5-groups* *bsk5-capacity*)))
(defun bsk5-linked-2 () (nth 8 (bsk5-record-2-run)))

(local
 (defthm bsk5-legal-choice-constructs-crash-image
   (implies (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs))
            (fn-bs-crash-imagep bs (fn-bs-crash bs choices)))
   :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff
                                    (s bs) (image (fn-bs-crash bs choices))))))))

(assert-event
 (let* ((pair (bsk5-linked)) (bs (car pair)) (ks (cdr pair))
        (lost (fn-bs-crash bs '(:drop)))
        (kept (fn-bs-crash bs '(:drop :drop :drop :drop :drop :drop :drop :apply))))
   (and (fn-bs-store-relation bs ks *bsk5-arena*)
        (fn-bs-crash-choicesp '(:drop) (fn-bs-pending bs) (fn-bs-unit bs))
        (fn-bs-crash-choicesp '(:drop :drop :drop :drop :drop :drop :drop :apply)
                              (fn-bs-pending bs) (fn-bs-unit bs))
        (equal (fn-bs-durable-records bs) nil)
        (equal (fn-bs-scan-records (fn-bs-scan-store lost)) nil)
        (equal (fn-bs-scan-records (fn-bs-scan-store kept))
               (list *bsk5-record*)))))

; A nonempty durable prefix survives the publication uncertainty of a
; second actual P-RECORD.  The two modeled crash choices preserve one or
; two complete decoded frames, never a synthetic or partial record.
(assert-event
 (let* ((pair (bsk5-linked-2)) (bs (car pair)) (ks (cdr pair))
        (old (fn-bs-crash bs nil))
        (new (fn-bs-crash bs '(:drop :drop :drop :apply)))
        (durable (fn-bs-durable-records bs)))
   (and (fn-bs-store-relation bs ks *bsk5-arena*)
        (equal durable (list *bsk5-record*))
        (fn-bs-crash-choicesp nil (fn-bs-pending bs) (fn-bs-unit bs))
        (fn-bs-crash-choicesp '(:drop :drop :drop :apply)
                              (fn-bs-pending bs) (fn-bs-unit bs))
        (equal (fn-bs-scan-records (fn-bs-scan-store old)) durable)
        (equal (fn-bs-scan-records (fn-bs-scan-store new))
               (list *bsk5-record* *bsk5-record-2*))
        (fn-sf-prefixp durable (fn-bs-scan-records (fn-bs-scan-store new))))))

; Without the relation, a physically well-shaped state can have two pending
; transaction links beyond an empty durable prefix.  Applying both violates
; the one-extra-record bound.  The inode octets came from the two actual
; completed write programs above; only the invalid pending publication shape
; is synthesized here.
(defun bsk5-two-pending ()
  (let* ((bs (car (bsk5-linked-2)))
         (first (fn-bs-durable-entry bs :transactions (fn-bs-txn-name 0)))
         (second (fn-bs-lookup bs :transactions (fn-bs-txn-name 1))))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs)
                (fn-bs-put-assoc :transactions nil (fn-bs-dirs bs))
                (list (list :set-entry :transactions (fn-bs-txn-name 0) first)
                      (list :set-entry :transactions (fn-bs-txn-name 1) second))
                (fn-bs-next-ino bs))))

(assert-event
 (let* ((bs (bsk5-two-pending))
        (image (fn-bs-crash bs '(:apply :apply))))
   (and (fn-bs-statep bs)
        (fn-bs-crash-choicesp '(:apply :apply)
                              (fn-bs-pending bs) (fn-bs-unit bs))
        (equal (fn-bs-durable-records bs) nil)
        (equal (fn-bs-scan-records (fn-bs-scan-store image))
               (list *bsk5-record* *bsk5-record-2*))
        (not (fn-bs-store-relation bs (cdr (bsk5-linked-2)) *bsk5-arena*)))))
(must-fail
 (assert-event
  (let* ((bs (bsk5-two-pending))
         (image (fn-bs-crash bs '(:apply :apply))))
    (<= (len (fn-bs-scan-records (fn-bs-scan-store image)))
        (1+ (len (fn-bs-durable-records bs)))))))

; Conversely, a related byte state cannot treat the two-record image as a
; crash image of its first publication.  Removing crash-imagep admits a
; concrete counterexample even with the byte/kernel relation preserved.
(assert-event (fn-bs-store-relation (car (bsk5-linked))
                                    (cdr (bsk5-linked)) *bsk5-arena*))
(must-fail
 (assert-event
  (let* ((bs (car (bsk5-linked)))
         (image (fn-bs-crash (bsk5-two-pending) '(:apply :apply))))
    (<= (len (fn-bs-scan-records (fn-bs-scan-store image)))
        (1+ (len (fn-bs-durable-records bs)))))))
