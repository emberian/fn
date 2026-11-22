; One semantic member leaf is the exact contiguous record-header/body range
; for one event. The physical frame reader authenticates the input window;
; this scanner enforces its declared member range and canonical boundaries.
(in-package "ACL2")
(include-book "journal-record-body")
(fn2-book-layer :c)

(include-book "journal-members-state")

(local (in-theory (disable fn2-journal-membersp fn2-journal-members-wfp fn2-journal-members-rows
                           fn2-journal-members-phase fn2-journal-members-next-event fn2-journal-members-end-event
                           fn2-journal-members-event fn2-journal-members-off fn2-journal-members-end
                           fn2-journal-members-start fn2-journal-members-leaf-end
                           fn2-fieldsp fn2-fields-wfp fn2-fields-rows fn2-poolp fn2-pool-wfp)))

(defun fn2-journal-members-begin (first members off end slot gen okind oslot ogen fn2-journal-members)
 (declare (xargs :stobjs fn2-journal-members :guard (fn2-journal-members-wfp fn2-journal-members)))
 (if (not (and (< 0 (fn2-journal-members-rows fn2-journal-members))
               (posp first) (posp members) (unsigned-byte-p 60 (+ first members))
               (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (< off end) (<= end 4096)
               (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
               (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
     (mv :bounds fn2-journal-members)
   (let ((fn2-journal-members (fn2-journal-members-put 0
            (phase *fn2-journal-members-phase-scanning*) (next-event first) (end-event (+ first members))
            (event 0) (off off) (end end) (start off) (leaf-end off) (hash-phase 0)
            (slot slot) (gen gen) (owner-kind okind) (owner-slot oslot) (owner-gen ogen))))
    (mv :ok fn2-journal-members))))
(fn2-journal-members-preserves fn2-journal-members-begin
 (first members off end slot gen okind oslot ogen fn2-journal-members) :position 1)

(defun fn2-journal-members-step (base fn2-journal-members fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-journal-members fn2-fields fn2-pool)
                 :guard (and (fn2-journal-members-wfp fn2-journal-members)
                             (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (< 0 (fn2-journal-members-rows fn2-journal-members)))
       (mv :bounds fn2-journal-members fn2-fields))
      (phase (fn2-journal-members-phase 0 fn2-journal-members))
      ((when (= phase *fn2-journal-members-phase-leaf*)) (mv :leaf fn2-journal-members fn2-fields))
      ((when (= phase *fn2-journal-members-phase-done*)) (mv :done fn2-journal-members fn2-fields))
      ((unless (= phase *fn2-journal-members-phase-scanning*)) (mv :state fn2-journal-members fn2-fields))
      (off (fn2-journal-members-off 0 fn2-journal-members))
      (end (fn2-journal-members-end 0 fn2-journal-members))
      (event (fn2-journal-members-event 0 fn2-journal-members))
      (expected (fn2-journal-members-next-event 0 fn2-journal-members))
      (limit (fn2-journal-members-end-event 0 fn2-journal-members))
      ((mv code next found & fn2-fields)
       (fn2-journal-record-next base (fn2-journal-members-slot 0 fn2-journal-members)
         (fn2-journal-members-gen 0 fn2-journal-members) off end
         (fn2-journal-members-owner-kind 0 fn2-journal-members)
         (fn2-journal-members-owner-slot 0 fn2-journal-members)
         (fn2-journal-members-owner-gen 0 fn2-journal-members) fn2-fields fn2-pool))
      (valid (or (and (eq code :end) (or (< 0 event) (= expected limit)))
                 (and (eq code :record) (natp found) (unsigned-byte-p 32 next) (< off next)
                      (< found limit)
                      (if (= event 0) (= found expected)
                        (or (= found event) (= found (+ event 1)))))))
      ((unless valid)
       (let ((fn2-journal-members (fn2-journal-members-set-phase 0 *fn2-journal-members-phase-invalid* fn2-journal-members)))
        (mv :invalid fn2-journal-members fn2-fields)))
      ((when (and (eq code :end) (= event 0)))
       (let ((fn2-journal-members (fn2-journal-members-set-phase 0 *fn2-journal-members-phase-done* fn2-journal-members)))
        (mv :done fn2-journal-members fn2-fields)))
      ((when (or (eq code :end) (and (< 0 event) (not (= found event)))))
       ; Do not consume the next member's first header. The ready leaf owns
       ; exactly START..OFF, and its bytes remain held while hashing/persisting.
       (let ((fn2-journal-members (fn2-journal-members-put 0
                (phase *fn2-journal-members-phase-leaf*) (leaf-end off) (hash-phase 0))))
        (mv :leaf fn2-journal-members fn2-fields))))
  (let ((fn2-journal-members
          (if (= event 0)
              (fn2-journal-members-put 0 (event found) (start off) (off next))
            (fn2-journal-members-set-off 0 next fn2-journal-members))))
   (mv :more fn2-journal-members fn2-fields))))
(fn2-journal-members-preserves fn2-journal-members-step (base fn2-journal-members fn2-fields fn2-pool)
 :carriers ((fn2-journal-members 1 :prefix "-MEMBERS") (fn2-fields 2 :prefix "-FIELDS")))

; A leaf consumer calls this only after its exact range was appended to the
; frontier/archive. There is no operation that skips a member or marks a
; positive event range complete without inspecting its records.
(defun fn2-journal-members-consumed (fn2-journal-members)
 (declare (xargs :stobjs fn2-journal-members :guard (fn2-journal-members-wfp fn2-journal-members)))
 (if (not (and (< 0 (fn2-journal-members-rows fn2-journal-members))
               (= (fn2-journal-members-phase 0 fn2-journal-members) *fn2-journal-members-phase-leaf*)
               (< (fn2-journal-members-start 0 fn2-journal-members) (fn2-journal-members-leaf-end 0 fn2-journal-members))
               (= (fn2-journal-members-event 0 fn2-journal-members) (fn2-journal-members-next-event 0 fn2-journal-members))
               (unsigned-byte-p 60 (+ 1 (fn2-journal-members-event 0 fn2-journal-members)))))
     (mv :state fn2-journal-members)
   (let* ((next (+ 1 (fn2-journal-members-event 0 fn2-journal-members)))
          (off (fn2-journal-members-off 0 fn2-journal-members))
          (fn2-journal-members (fn2-journal-members-put 0
            (phase *fn2-journal-members-phase-scanning*)
            (next-event next) (event 0) (hash-phase 0) (start off))))
    (mv :ok fn2-journal-members))))
(fn2-journal-members-preserves fn2-journal-members-consumed (fn2-journal-members) :position 1)
