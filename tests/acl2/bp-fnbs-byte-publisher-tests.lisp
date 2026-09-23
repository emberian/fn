; Actual FNBS kind-5 frame through byte-store publication and crash cuts.
(in-package "ACL2")
(include-book "../../books/bp-fnbs-byte-invariants")
(include-book "bp-fnbs-codec-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-bpnf-byte-test-base ()
  (fn-bs-make 4
              (list (cons 0 (fn-bpnf-stored-record-frame *bpnfc-record*)))
              (list (cons :fnbs
                          (list (cons (fn-bpnf-stored-record-name 9 0) 0))))
              nil 1))

(defun fn-bpnf-byte-test-cuts ()
  (fn-bpnf-byte-cuts
   (fn-bpnf-byte-test-base) ".kind5-stage"
   (fn-bpnf-stored-record-name 9 1)
   (fn-bpnf-stored-record-frame *bpnfc-anon-record*)))

(defun fn-bpnf-byte-test-state (phase)
  (fn-bpnf-byte-cut (fn-bpnf-byte-test-cuts) phase))

(assert-event (fn-bs-statep (fn-bpnf-byte-test-base)))
(assert-event
 (equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-base) 9 0)
        (list :record *bpnfc-record*)))
(assert-event
 (equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-base) 9 1) :absent))

; The private stage may be visible with no landed write at a pre-fence cut.
; It cannot be mistaken for a public kind-5 record.
(defun fn-bpnf-byte-test-torn-stage ()
  (fn-bs-crash (fn-bpnf-byte-test-state :write) '(:apply nil)))
(assert-event
 (fn-bs-crash-choicesp '(:apply nil)
                       (fn-bs-pending (fn-bpnf-byte-test-state :write)) 4))
(assert-event
 (equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-torn-stage) 9 1) :absent))
(assert-event
 (equal (fn-bs-durable-content
         (fn-bpnf-byte-test-torn-stage)
         (fn-bs-durable-entry (fn-bpnf-byte-test-torn-stage)
                              :fnbs ".kind5-stage"))
        nil))

; After file fsync but before the directory barrier, either absence or the
; exact fenced frame is a possible physical crash image.
(defun fn-bpnf-byte-test-link-absent ()
  (fn-bs-crash (fn-bpnf-byte-test-state :link) nil))
(defun fn-bpnf-byte-test-link-present ()
  (fn-bs-crash (fn-bpnf-byte-test-state :link) '(:drop :apply)))
(assert-event
 (fn-bs-crash-choicesp '(:drop :apply)
                       (fn-bs-pending (fn-bpnf-byte-test-state :link)) 4))
(assert-event
 (equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-link-absent) 9 1) :absent))
(assert-event
 (equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-link-present) 9 1)
        (list :record *bpnfc-anon-record*)))
(assert-event
 (let* ((fenced (fn-bpnf-byte-test-state :file-barrier))
        (linked (fn-bpnf-byte-test-state :link))
        (ino (fn-bs-lookup fenced :fnbs ".kind5-stage"))
        (name (fn-bpnf-stored-record-name 9 1))
        (frame (fn-bpnf-stored-record-frame *bpnfc-anon-record*)))
   (and (fn-bs-inop ino)
        (fn-bs-fencedp fenced ino)
        (equal (fn-bs-durable-content fenced ino) frame)
        (equal (fn-bs-durable-entry fenced :fnbs name) nil)
        (equal (fn-bs-ops-for-name (fn-bs-pending fenced) :fnbs name) nil)
        (equal linked (fn-bpnf-byte-test-state :link))
        (member-equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-link-absent) 9 1)
                      (list :absent (list :record *bpnfc-anon-record*)))
        (member-equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-link-present) 9 1)
                      (list :absent (list :record *bpnfc-anon-record*))))))
(must-fail
 (assert-event
  (equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-link-absent) 9 1)
         (fn-bpnf-byte-slot (fn-bpnf-byte-test-link-present) 9 1))))

; Successful directory barrier makes the second record authority.  An
; uncertainty callback, by contrast, leaves A1's issued operation fenced
; even if the byte outcome happens to contain the final name.
(defun fn-bpnf-byte-test-durable-crash ()
  (fn-bs-crash (fn-bpnf-byte-test-state :directory-barrier) nil))
(assert-event
 (equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-durable-crash) 9 0)
        (list :record *bpnfc-record*)))
(assert-event
 (equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-durable-crash) 9 1)
        (list :record *bpnfc-anon-record*)))
(assert-event
 (let* ((durable (fn-bpnf-byte-test-state :directory-barrier))
        (ino (fn-bs-durable-entry
              durable :fnbs (fn-bpnf-stored-record-name 9 1))))
   (and (fn-bs-dir-quietp durable :fnbs)
        (fn-bs-fencedp durable ino)
        (equal (fn-bs-crash durable nil)
               (fn-bpnf-byte-test-durable-crash))
        (equal (fn-bs-durable-content durable ino)
               (fn-bpnf-stored-record-frame *bpnfc-anon-record*)))))
(must-fail
 (assert-event
  (equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-durable-crash) 9 1)
         :absent)))
(assert-event
 (equal (fn-jpub-outcome (fn-bpnf-byte-publisher-phase :directory-barrier))
        :durable))
(assert-event
 (equal (fn-jpub-outcome
         (fn-jpub-step (fn-bpnf-byte-link-phase)
                       '(:directory-barrier-result :error)))
        :uncertain))
(assert-event
 (equal (nth 5 (fn-bpnf-issued
                  (fn-bpnf-answer-state
                   (fn-bpnf-step (fn-bpnf-answer-state *bpnfc-proposal*)
                                 '(:persist-result 9 0 :uncertain)))))
        :uncertain))

; An occupied final name containing garbage is a fault, not an empty slot.
(defun fn-bpnf-byte-test-garbage ()
  (fn-bs-make 4 '((0 1 2 3))
              (list (cons :fnbs
                          (list (cons (fn-bpnf-stored-record-name 9 1) 0))))
              nil 1))
(assert-event
 (equal (fn-bpnf-byte-slot (fn-bpnf-byte-test-garbage) 9 1)
        '(:fault :occupied-damaged)))
