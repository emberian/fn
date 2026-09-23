; Counterexamples that constrain the FNBS A2 byte/replay contract.
; The kind-1 sequence frame is a real FNBS frame, not an article Store frame.
; A2's kind-5 publisher will use the same magic and crash predicate.
(in-package "ACL2")
(include-book "../../books/bp-node-records")
(include-book "../../books/byte-store-invariants")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-bpnf-byte-inherited-frame ()
  (fn-bpn-sequence-record-frame (fn-bpn-sequence-record 1)))
(defun fn-bpnf-byte-inherited ()
  (fn-bs-make 4
              (list (cons 0 (fn-bpnf-byte-inherited-frame)))
              (list (cons :fnbs (list (cons "frontier.fnb" 0))))
              nil 1))
(defun fn-bpnf-byte-zero-event-crash ()
  (fn-bs-crash (fn-bpnf-byte-inherited) nil))

; A successful nonempty inherited byte history stays nonempty after a crash
; even when the new process epoch issues zero events.  A suffix-only scan
; equation that equates the entire directory with an empty delta is false.
(defthm fn-bpnf-byte-zero-event-crash-is-admissible
 (fn-bs-crash-imagep (fn-bpnf-byte-inherited)
                     (fn-bpnf-byte-zero-event-crash))
  :hints (("Goal" :use ((:instance fn-bs-lose-everything-is-an-admissible-image
                                   (s (fn-bpnf-byte-inherited)))))))
(assert-event
 (equal (fn-bpn-sequence-record-unframe
         (fn-bs-content (fn-bpnf-byte-zero-event-crash)
                        (fn-bs-lookup (fn-bpnf-byte-zero-event-crash)
                                      :fnbs "frontier.fnb")))
        (fn-bpn-sequence-record 1)))
(must-fail
 (assert-event
  (null (fn-bs-lookup (fn-bpnf-byte-zero-event-crash)
                      :fnbs "frontier.fnb"))))

; A second process death does not erase inherited authority.  This is the
; minimum byte-level second-crash shape that A2's full replay must retain.
(defun fn-bpnf-byte-second-crash ()
  (fn-bs-crash (fn-bpnf-byte-zero-event-crash) nil))
(defthm fn-bpnf-byte-second-crash-is-admissible
 (fn-bs-crash-imagep (fn-bpnf-byte-zero-event-crash)
                     (fn-bpnf-byte-second-crash))
  :hints (("Goal" :use ((:instance fn-bs-lose-everything-is-an-admissible-image
                                   (s (fn-bpnf-byte-zero-event-crash)))))))
(assert-event
 (equal (fn-bs-content (fn-bpnf-byte-second-crash)
                       (fn-bs-lookup (fn-bpnf-byte-second-crash)
                                     :fnbs "frontier.fnb"))
        (fn-bpnf-byte-inherited-frame)))

; Occupied authority with malformed bytes is not an absent publication.
; Recovery must fault instead of silently dropping this name.
(defun fn-bpnf-byte-garbage ()
  (fn-bs-make 4 '((0 1 2 3))
              '((:fnbs ("frontier.fnb" . 0))) nil 1))
(assert-event
 (and (fn-bs-lookup (fn-bpnf-byte-garbage) :fnbs "frontier.fnb")
      (null (fn-bpn-sequence-record-unframe
             (fn-bs-content (fn-bpnf-byte-garbage)
                            (fn-bs-lookup (fn-bpnf-byte-garbage)
                                          :fnbs "frontier.fnb"))))))
(must-fail
 (assert-event
  (null (fn-bs-lookup (fn-bpnf-byte-garbage) :fnbs "frontier.fnb"))))
