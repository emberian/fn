; Teeth for books/store-mount-identity.lisp (PRF-232, PKT-579).
(in-package "ACL2")
(include-book "../../books/store-mount-identity")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; Reachable witnesses: the mountinfo lines hbox prints for a loop-mounted
; ext4 node volume over the ext4 root, and the store under it.

(defconst *smid-t-path* (fn-smid-text "/srv/fn-public/store"))
(defconst *smid-t-root-line*
  (fn-smid-text "22 1 259:4 / / rw,relatime shared:1 - ext4 /dev/nvme0n1p4 rw,errors=remount-ro"))
(defconst *smid-t-volume-line*
  (fn-smid-text "40 22 7:0 / /srv/fn-public rw,relatime shared:9 - ext4 /dev/loop0 rw"))
; A sibling whose name the store path extends as text but not as a path.
(defconst *smid-t-sibling-line*
  (fn-smid-text "41 22 7:1 / /srv/fn rw,relatime shared:10 - ext4 /dev/loop1 rw"))
; An escaped mount point (a space in the name).
(defconst *smid-t-escaped-line*
  (fn-smid-text "42 22 7:2 / /srv/a\\040b rw - ext4 /dev/loop2 rw,nobarrier"))

(defconst *smid-t-mounted-best*
  (fn-smid-mountinfo-step
   (fn-smid-mountinfo-step
    (fn-smid-mountinfo-step nil *smid-t-root-line* *smid-t-path*)
    *smid-t-volume-line* *smid-t-path*)
   *smid-t-sibling-line* *smid-t-path*))
(defconst *smid-t-unmounted-best*
  (fn-smid-mountinfo-step
   (fn-smid-mountinfo-step nil *smid-t-root-line* *smid-t-path*)
   *smid-t-sibling-line* *smid-t-path*))

(assert-event (equal (car *smid-t-mounted-best*) (fn-smid-text "/srv/fn-public")))
(assert-event (equal (car *smid-t-unmounted-best*) (fn-smid-text "/")))
(assert-event (equal (car (fn-smid-mountinfo-entry *smid-t-escaped-line*))
                     (fn-smid-text "/srv/a b")))
(assert-event (not (fn-smid-mount-containsp (fn-smid-text "/srv/fn") *smid-t-path*)))
(assert-event (fn-smid-mount-containsp (fn-smid-text "/srv/fn-public") *smid-t-path*))
(assert-event (equal (fn-smid-mountinfo-step *smid-t-mounted-best* :overlong *smid-t-path*)
                     :overlong))

(defconst *smid-t-fsid* '(17 34 51 68 85 102 119 136))
(defconst *smid-t-root-fsid* '(1 2 3 4 5 6 7 8))
(defconst *smid-t-mounted*
  (fn-smid-linux-observation *smid-t-fsid* *smid-t-mounted-best*))
(defconst *smid-t-unmounted*
  (fn-smid-linux-observation *smid-t-root-fsid* *smid-t-unmounted-best*))
; The same volume after a remount on another loop device: same fsid.
(defconst *smid-t-remounted*
  (fn-smid-linux-observation
   *smid-t-fsid*
   (fn-smid-mountinfo-step
    (fn-smid-mountinfo-step nil *smid-t-root-line* *smid-t-path*)
    (fn-smid-text "43 22 7:5 / /srv/fn-public rw,relatime - ext4 /dev/loop5 rw")
    *smid-t-path*)))
; Another volume mounted at the same point: another fsid.
(defconst *smid-t-other-volume*
  (fn-smid-linux-observation '(9 9 9 9 9 9 9 9) *smid-t-mounted-best*))

(assert-event (fn-smid-observationp *smid-t-mounted*))
(assert-event (fn-smid-observationp *smid-t-unmounted*))
(assert-event (fn-smid-observationp *smid-t-remounted*))
(assert-event (equal (fn-smid-linux-observation *smid-t-fsid* :overlong)
                     (list :unobserved)))
(assert-event (equal (fn-smid-linux-observation *smid-t-fsid* nil)
                     (list :unobserved)))

(defconst *smid-t-plan* (fn-smid-record-plan *smid-t-mounted* 1))
(defconst *smid-t-protected* (cadr *smid-t-plan*))
; A sealed record carries ACL2's trailer, which evaluates under the digest
; attachment in an assertion but not in a defconst: these are macros.
(defmacro smid-t-record () '(fn-smid-sealed *smid-t-protected*))
(assert-event (equal (car *smid-t-plan*) :record))
(assert-event (consp *smid-t-protected*))

; -----------------------------------------------------------------------------
; fn-smid-record-decode-of-seal: the witness, and the hypothesis.

(defconst *smid-t-id* (fn-smid-observed-identity *smid-t-mounted*))
(defconst *smid-t-rec* (fn-smid-observed-record *smid-t-mounted* 1))
(assert-event (fn-smid-recordp *smid-t-rec*))
(assert-event (equal (fn-smid-record-decode
                      (append (fn-smid-record-protected *smid-t-rec*)
                              (fn-frame-trailer (fn-smid-record-protected *smid-t-rec*)))
                      (fn-frame-trailer (fn-smid-record-protected *smid-t-rec*)))
                     *smid-t-rec*))
; Without (fn-smid-recordp id): a three-field list is no record, and the
; conclusion fails on it.
(assert-event (not (fn-smid-recordp '(nil nil nil))))
(assert-event (not (equal (fn-smid-record-decode
                           (append (fn-smid-record-protected '(nil nil nil))
                                   (fn-frame-trailer (fn-smid-record-protected '(nil nil nil))))
                           (fn-frame-trailer (fn-smid-record-protected '(nil nil nil))))
                          '(nil nil nil))))
(must-fail
 (defthm smid-t-decode-of-seal-without-recordp
   (equal (fn-smid-record-decode
           (append (fn-smid-record-protected id)
                   (fn-frame-trailer (fn-smid-record-protected id)))
           (fn-frame-trailer (fn-smid-record-protected id)))
          id)))

; A flipped octet in the file does not decode (the trailer is ACL2's).
(assert-event
 (let* ((octets (cadr (smid-t-record)))
        (bad (update-nth 20 (mod (+ 1 (nth 20 octets)) 256) octets)))
   (equal (fn-smid-open-verdict
           (list :present bad
                 (fn-frame-trailer (take (- (len bad) 32) bad)))
           *smid-t-mounted*)
          (list :refused :filesystem-record-invalid *smid-t-id*))))

; -----------------------------------------------------------------------------
; fn-smid-recorded-store-opens-iff-same-filesystem: positive witnesses (both
; sides true; both sides false), and one failure per hypothesis.

(assert-event (equal (fn-smid-open-verdict (smid-t-record) *smid-t-mounted*)
                     (list :open)))
(assert-event (fn-smid-same-filesystemp *smid-t-id* *smid-t-id*))
(assert-event (equal (fn-smid-open-verdict (smid-t-record) *smid-t-remounted*)
                     (list :open)))
(assert-event (not (equal (nth 4 *smid-t-remounted*) (nth 4 *smid-t-mounted*))))
(assert-event (not (equal (fn-smid-open-verdict (smid-t-record) *smid-t-other-volume*)
                          (list :open))))
(assert-event (not (fn-smid-same-filesystemp
                    *smid-t-id* (fn-smid-observed-identity *smid-t-other-volume*))))

; Without (fn-smid-observationp obs2): the same four fields with options
; that are not octets name the same filesystem, yet the open is refused.
(defconst *smid-t-bad-obs*
  (list :observed (nth 1 *smid-t-mounted*) (nth 2 *smid-t-mounted*)
        (nth 3 *smid-t-mounted*) (nth 4 *smid-t-mounted*) '(300)))
(assert-event (not (fn-smid-observationp *smid-t-bad-obs*)))
(assert-event (fn-smid-same-filesystemp
               *smid-t-id* (fn-smid-observed-identity *smid-t-bad-obs*)))
(assert-event (equal *smid-t-plan* (list :record *smid-t-protected*)))
(assert-event (equal (fn-smid-open-verdict (smid-t-record) *smid-t-bad-obs*)
                     (list :refused :filesystem-unobserved)))

; Without the plan: bytes that are no record do not open the same filesystem.
(assert-event (not (equal (fn-smid-record-plan *smid-t-mounted* 1) (list :record nil))))
(assert-event (equal (fn-smid-open-verdict (fn-smid-sealed nil) *smid-t-mounted*)
                     (list :refused :filesystem-record-invalid *smid-t-id*)))
(must-fail
 (defthm smid-t-opens-iff-without-plan
   (implies (fn-smid-observationp obs2)
            (equal (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs2)
                          (list :open))
                   (fn-smid-same-filesystemp (fn-smid-observed-identity obs)
                                             (fn-smid-observed-identity obs2))))))

; -----------------------------------------------------------------------------
; fn-smid-moved-mount-point-is-refused-by-name: the missing mount.

(assert-event (not (equal (nth 3 *smid-t-mounted*) (nth 3 *smid-t-unmounted*))))
(assert-event (equal (fn-smid-open-verdict (smid-t-record) *smid-t-unmounted*)
                     (list :refused :filesystem-changed *smid-t-rec*
                           (fn-smid-observed-identity *smid-t-unmounted*))))
; Without the differing mount point: the mount point agrees and it opens.
(assert-event (equal (nth 3 *smid-t-mounted*) (nth 3 *smid-t-remounted*)))
(assert-event (not (equal (fn-smid-open-verdict (smid-t-record) *smid-t-remounted*)
                          (list :refused :filesystem-changed *smid-t-rec*
                                (fn-smid-observed-identity *smid-t-remounted*)))))
(must-fail
 (defthm smid-t-moved-without-mount-difference
   (implies (and (fn-smid-observationp obs2)
                 (equal (fn-smid-record-plan obs policy) (list :record protected)))
            (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs2)
                   (list :refused :filesystem-changed
                         (fn-smid-observed-record obs policy)
                         (fn-smid-observed-identity obs2))))))
; Without (fn-smid-observationp obs2): refused, but as unobserved.
(defconst *smid-t-bad-moved*
  (list :observed (nth 1 *smid-t-unmounted*) (nth 2 *smid-t-unmounted*)
        (nth 3 *smid-t-unmounted*) (nth 4 *smid-t-unmounted*) '(300)))
(assert-event (not (equal (fn-smid-open-verdict (smid-t-record) *smid-t-bad-moved*)
                          (list :refused :filesystem-changed *smid-t-rec*
                                (fn-smid-observed-identity *smid-t-bad-moved*)))))
(must-fail
 (defthm smid-t-moved-without-observation
   (implies (and (equal (fn-smid-record-plan obs policy) (list :record protected))
                 (not (equal (nth 3 obs) (nth 3 obs2))))
            (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs2)
                   (list :refused :filesystem-changed
                         (fn-smid-observed-record obs policy)
                         (fn-smid-observed-identity obs2))))))
; Without the plan: an invalid record is refused as invalid, not as changed.
(assert-event (equal (car (cdr (fn-smid-open-verdict (fn-smid-sealed nil)
                                                     *smid-t-unmounted*)))
                     :filesystem-record-invalid))
(must-fail
 (defthm smid-t-moved-without-plan
   (implies (and (fn-smid-observationp obs2)
                 (not (equal (nth 3 obs) (nth 3 obs2))))
            (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs2)
                   (list :refused :filesystem-changed
                         (fn-smid-observed-record obs policy)
                         (fn-smid-observed-identity obs2))))))

; -----------------------------------------------------------------------------
; fn-smid-absent-record-is-refused, both arms reached.

(assert-event (equal (fn-smid-open-verdict (list :absent) *smid-t-unmounted*)
                     (list :refused :filesystem-unrecorded
                           (fn-smid-observed-identity *smid-t-unmounted*))))
(assert-event (equal (fn-smid-open-verdict (list :absent) (list :unobserved))
                     (list :refused :filesystem-unobserved)))

; fn-smid-open-verdict-opens-only-on-a-match on the witness.
(assert-event (fn-smid-same-filesystemp
               (fn-smid-record-decode (nth 1 (smid-t-record)) (nth 2 (smid-t-record)))
               (fn-smid-observed-identity *smid-t-mounted*)))

; -----------------------------------------------------------------------------
; fn-smid-mountinfo-step-preserves-best-okp: the witness and the hypothesis.

(assert-event (fn-smid-best-okp *smid-t-mounted-best* *smid-t-path*))
(assert-event (fn-smid-best-okp *smid-t-unmounted-best* *smid-t-path*))
; Without (fn-smid-best-okp best path): a best that does not contain the
; path survives a line that does not replace it.
(defconst *smid-t-foreign-best*
  (fn-smid-mountinfo-entry *smid-t-sibling-line*))
(assert-event (not (fn-smid-best-okp *smid-t-foreign-best* *smid-t-path*)))
(assert-event (not (fn-smid-best-okp
                    (fn-smid-mountinfo-step *smid-t-foreign-best*
                                            *smid-t-escaped-line* *smid-t-path*)
                    *smid-t-path*)))
(must-fail
 (defthm smid-t-step-without-best-okp
   (fn-smid-best-okp (fn-smid-mountinfo-step best line path) path)))

; -----------------------------------------------------------------------------
; The texts: the refusal is ACL2's line, NIL exactly for (:open).

(assert-event (null (fn-smid-refusal-text (list :open))))
(assert-event (equal (fn-smid-refusal-text
                      (fn-smid-open-verdict (smid-t-record) *smid-t-unmounted*))
                     (fn-smid-text "store filesystem changed: expected ext4 at /srv/fn-public from /dev/loop0 (fsid 1122334455667788), found ext4 at / from /dev/nvme0n1p4 (fsid 0102030405060708); mount the node volume or run `store rebind-filesystem` after moving the store deliberately")))
(assert-event (equal (fn-smid-display (list 97 92 10 255))
                     (fn-smid-text "a\\x5c\\x0a\\xff")))
(assert-event (consp (fn-smid-rebind-text (smid-t-record) *smid-t-unmounted* nil)))

; The durability warning (PKT-648): nobarrier and tmpfs warn; plain does not.
(assert-event (null (fn-smid-durability-warning *smid-t-mounted*)))
(assert-event (consp (fn-smid-durability-warning
                      (fn-smid-linux-observation
                       *smid-t-fsid*
                       (fn-smid-mountinfo-entry *smid-t-escaped-line*)))))
(assert-event (consp (fn-smid-durability-warning
                      (list :observed '(0) (fn-smid-text "tmpfs") (fn-smid-text "/dev/shm")
                            (fn-smid-text "tmpfs") nil))))

; OpenBSD: statfs names the mount; an unprivileged fsid is zeros and the
; source stands in for it.
(defconst *smid-t-bsd*
  (fn-smid-statfs-observation '(0 0 0 0 0 0 0 0) (fn-smid-text "ffs")
                              (fn-smid-text "/home") (fn-smid-text "/dev/sd0k")))
(defconst *smid-t-bsd-other*
  (fn-smid-statfs-observation '(0 0 0 0 0 0 0 0) (fn-smid-text "ffs")
                              (fn-smid-text "/home") (fn-smid-text "/dev/vnd0a")))
(assert-event (equal (fn-smid-open-verdict
                      (fn-smid-sealed (cadr (fn-smid-record-plan *smid-t-bsd* 1)))
                      *smid-t-bsd*)
                     (list :open)))
(assert-event (equal (car (cdr (fn-smid-open-verdict
                                (fn-smid-sealed (cadr (fn-smid-record-plan *smid-t-bsd* 1)))
                                *smid-t-bsd-other*)))
                     :filesystem-changed))

; -----------------------------------------------------------------------------
; fn-smid-start-refused-iff-required-and-unsafe (PKT-648).

; A tmpfs store and a nobarrier store, each recorded under both policies.
(defconst *smid-t-tmpfs*
  (fn-smid-linux-observation
   '(0 0 0 0 0 0 0 0)
   (fn-smid-mountinfo-step
    nil (fn-smid-text "30 22 0:26 / /tmp rw,nosuid,nodev - tmpfs tmpfs rw,size=64659820k")
    (fn-smid-text "/tmp/fn-test/store"))))
(defconst *smid-t-nobarrier*
  (fn-smid-linux-observation
   *smid-t-fsid*
   (fn-smid-mountinfo-step
    nil (fn-smid-text "40 22 7:0 / /srv/fn-public rw,relatime - ext4 /dev/loop0 rw,nobarrier")
    *smid-t-path*)))
(assert-event (equal (fn-smid-unsafe-reason *smid-t-tmpfs*) :memory))
(assert-event (equal (fn-smid-unsafe-reason *smid-t-nobarrier*) :nobarrier))
(assert-event (null (fn-smid-unsafe-reason *smid-t-mounted*)))

(defmacro smid-t-sealed-plan (obs policy)
  `(fn-smid-sealed (cadr (fn-smid-record-plan ,obs ,policy))))

; Required and unsafe: refused by name, both reasons.
(assert-event (equal (fn-smid-start-verdict (smid-t-sealed-plan *smid-t-tmpfs* 1) *smid-t-tmpfs*)
                     (list :refused :storage-not-durable :memory
                           (fn-smid-observed-identity *smid-t-tmpfs*))))
(assert-event (equal (fn-smid-start-verdict (smid-t-sealed-plan *smid-t-nobarrier* 1)
                                            *smid-t-nobarrier*)
                     (list :refused :storage-not-durable :nobarrier
                           (fn-smid-observed-identity *smid-t-nobarrier*))))
; Not required: starts, and the warning is still printed.
(assert-event (equal (fn-smid-start-verdict (smid-t-sealed-plan *smid-t-tmpfs* 0) *smid-t-tmpfs*)
                     (list :start)))
(assert-event (consp (fn-smid-durability-warning *smid-t-tmpfs*)))
; Required and safe: starts.
(assert-event (equal (fn-smid-start-verdict (smid-t-record) *smid-t-mounted*)
                     (list :start)))
; The init policy: 1 under a mission, 0 otherwise.
(assert-event (equal (fn-smid-init-policy "small-community") 1))
(assert-event (equal (fn-smid-init-policy nil) 0))

; Without the same filesystem: the start answers the open's refusal, not the
; policy's.
(assert-event (equal (fn-smid-start-verdict (smid-t-record) *smid-t-unmounted*)
                     (fn-smid-open-verdict (smid-t-record) *smid-t-unmounted*)))
(assert-event (not (equal (fn-smid-start-verdict (smid-t-record) *smid-t-unmounted*)
                          (list :start))))
(must-fail
 (defthm smid-t-start-without-same-filesystem
   (implies (and (fn-smid-observationp obs2)
                 (equal (fn-smid-record-plan obs policy) (list :record protected)))
            (equal (fn-smid-start-verdict (fn-smid-sealed protected) obs2)
                   (if (and (equal policy 1) (fn-smid-unsafe-reason obs2))
                       (list :refused :storage-not-durable
                             (fn-smid-unsafe-reason obs2)
                             (fn-smid-observed-identity obs2))
                     (list :start))))))
; Without (fn-smid-observationp obs2): the same fields with bad options are
; refused as unobserved.
(assert-event (not (equal (fn-smid-start-verdict (smid-t-record) *smid-t-bad-obs*)
                          (list :start))))
(must-fail
 (defthm smid-t-start-without-observation
   (implies (and (equal (fn-smid-record-plan obs policy) (list :record protected))
                 (fn-smid-same-filesystemp (fn-smid-observed-identity obs)
                                           (fn-smid-observed-identity obs2)))
            (equal (fn-smid-start-verdict (fn-smid-sealed protected) obs2)
                   (if (and (equal policy 1) (fn-smid-unsafe-reason obs2))
                       (list :refused :storage-not-durable
                             (fn-smid-unsafe-reason obs2)
                             (fn-smid-observed-identity obs2))
                     (list :start))))))
; Without the plan: no record, no start.
(assert-event (not (equal (fn-smid-start-verdict (fn-smid-sealed nil) *smid-t-mounted*)
                          (list :start))))
(must-fail
 (defthm smid-t-start-without-plan
   (implies (and (fn-smid-observationp obs2)
                 (fn-smid-same-filesystemp (fn-smid-observed-identity obs)
                                           (fn-smid-observed-identity obs2)))
            (equal (fn-smid-start-verdict (fn-smid-sealed protected) obs2)
                   (if (and (equal policy 1) (fn-smid-unsafe-reason obs2))
                       (list :refused :storage-not-durable
                             (fn-smid-unsafe-reason obs2)
                             (fn-smid-observed-identity obs2))
                     (list :start))))))

; -----------------------------------------------------------------------------
; fn-smid-rebound-store-opens: the missing-mount store, rebound deliberately
; onto the root filesystem, opens there; the policy is kept, or set.

(defmacro smid-t-rebind () '(fn-smid-rebind-plan (smid-t-record) *smid-t-unmounted* nil))
(assert-event (equal (car (smid-t-rebind)) :record))
(assert-event (equal (fn-smid-open-verdict (fn-smid-sealed (cadr (smid-t-rebind)))
                                           *smid-t-unmounted*)
                     (list :open)))
(assert-event (equal (fn-smid-rebind-policy (smid-t-record) nil) 1))
(assert-event (equal (fn-smid-rebind-policy (smid-t-sealed-plan *smid-t-tmpfs* 0) nil) 0))
(assert-event (equal (fn-smid-rebind-policy (smid-t-record) 0) 0))
(assert-event (equal (fn-smid-rebind-policy (list :absent) nil) 1))
; Without the plan: arbitrary bytes do not open.
(assert-event (not (equal (fn-smid-open-verdict (fn-smid-sealed nil) *smid-t-mounted*)
                          (list :open))))
(must-fail
 (defthm smid-t-rebound-without-plan
   (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs)
          (list :open))))

; -----------------------------------------------------------------------------
; The host's open decision: a store made before the record.

; fn-smid-open-decision-is-the-verdict: a recorded store, configured.
(assert-event (equal (fn-smid-open-decision (smid-t-record) *smid-t-mounted* t)
                     (fn-smid-open-verdict (smid-t-record) *smid-t-mounted*)))
(assert-event (equal (fn-smid-open-decision (smid-t-record) *smid-t-unmounted* t)
                     (fn-smid-open-verdict (smid-t-record) *smid-t-unmounted*)))
; Without the hypothesis: no record, configured, observed -- the decision
; opens the store made before the record while the verdict refuses it.
(assert-event (equal (fn-smid-open-decision (list :absent) *smid-t-mounted* t)
                     (list :open-unrecorded *smid-t-id*)))
(assert-event (not (equal (fn-smid-open-decision (list :absent) *smid-t-mounted* t)
                          (fn-smid-open-verdict (list :absent) *smid-t-mounted*))))
(must-fail
 (defthm smid-t-decision-without-hypothesis
   (equal (fn-smid-open-decision record observation configured)
          (fn-smid-open-verdict record observation))))

; fn-smid-empty-root-is-refused: the empty directory underneath a volume.
(assert-event (equal (fn-smid-open-decision (list :absent) *smid-t-unmounted* nil)
                     (list :refused :filesystem-unrecorded
                           (fn-smid-observed-identity *smid-t-unmounted*))))
; Without (not configured): a configured root with no record is opened.
(assert-event (not (equal (car (fn-smid-open-decision (list :absent) *smid-t-unmounted* t))
                          :refused)))
(must-fail
 (defthm smid-t-empty-root-without-hypothesis
   (equal (car (fn-smid-open-decision (list :absent) observation configured))
          :refused)))

; fn-smid-unrecorded-store-never-starts, on the witness; the warning names
; the remedy.
(assert-event (equal (fn-smid-start-verdict (list :absent) *smid-t-mounted*)
                     (list :refused :filesystem-unrecorded *smid-t-id*)))
(assert-event (consp (fn-smid-unrecorded-warning
                      (fn-smid-open-decision (list :absent) *smid-t-mounted* t))))
(assert-event (null (fn-smid-unrecorded-warning (list :open))))
(assert-event (null (fn-smid-refusal-text
                     (fn-smid-open-decision (list :absent) *smid-t-mounted* t))))
