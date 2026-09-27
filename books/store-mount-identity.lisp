; fn: the identity of the filesystem a Store lives on, required at every open
; (PKT-579, review 2026-09-26 section 8; PRF-232, STO-031).
;
; A node's Store belongs on a provisioned volume.  When that volume is not
; mounted, the store path resolves into the directory underneath it, on the
; filesystem that holds the mount point.  An open there must not proceed:
; it would serve (or start) a different history, or place a new one where
; the next mount hides it.  So `init' records the identity of the filesystem
; the Store was created on, and every open compares what the host observes
; now with that record.  ACL2 decides both: what the observation is (the
; Linux mount table line is parsed and selected here, never by the host) and
; whether it matches.  `store rebind-filesystem' records the current identity
; explicitly, for a deliberate move or a restored backup.
;
; The identity is four fields, each an octet string:
;
;   FSID    the kernel's filesystem id (statfs f_fsid, eight octets as the
;           kernel lays them out).  Linux ext4 derives it from the volume
;           UUID and ZFS from the dataset, so it survives a remount and a
;           reboot; OpenBSD reports zeros to an unprivileged process.
;   FSTYPE  the filesystem type (mountinfo's type field; statfs
;           f_fstypename on OpenBSD and macOS).
;   MOUNT   the mount point containing the store root (the mountinfo line
;           whose mount point is the longest component prefix of the root's
;           resolved path; f_mntonname on OpenBSD and macOS).
;   SOURCE  the mounted device or dataset (mountinfo's source field;
;           f_mntfromname).
;
; Two identities name the same filesystem (`fn-smid-same-filesystemp') when
; the types agree and, where both fsids are known (nonzero), the fsids agree;
; where either is unknown the mount point and the source stand in for it.
; Where both fsids are known neither the source nor the mount point is
; compared: a loop device number, or a /dev/sdX name, can change across a
; remount while the volume is the same, and the mount point is a property of
; the viewer's mount namespace, not of the filesystem (PKT-706, the stranger
; rehearsal of 2026-09-27).  The shipped systemd unit's ProtectSystem=strict
; with ReadWritePaths=/var/lib/fn bind-mounts /var/lib/fn onto itself in the
; service's namespace, so the service sees the store at a mount point
; /var/lib/fn that `init', run outside the unit, recorded as `/'.  The
; missing volume the record guards against still changes the fsid: the
; directory underneath lives on the filesystem that holds the mount point,
; whose fsid is another (`fn-smid-other-filesystem-is-refused-by-name').
;
; The host entries (host/store-host.lisp marshals nothing; host/native/io.lisp
; calls each directly through fnn-core):
;
;   * `fn-smid-mountinfo-step' BEST LINE PATH: one /proc/self/mountinfo line
;     folded into the best containing mount (io.lisp
;     `fnn-filesystem-observation', Linux);
;   * `fn-smid-linux-observation' FSID BEST and `fn-smid-statfs-observation'
;     FSID FSTYPE MOUNT SOURCE: the observation (io.lisp
;     `fnn-filesystem-observation');
;   * `fn-smid-open-decision' RECORD OBSERVATION CONFIGURED: the host's open,
;     which is `fn-smid-open-verdict' wherever a record is present
;     (`fn-smid-open-decision-is-the-verdict');
;   * `fn-smid-open-verdict' RECORD OBSERVATION: the open's decision (io.lisp
;     `fnn-check-filesystem-identity', called by `fnn-acquire', so every
;     open: owner start, recover, status, inspect, export, checkpoint, the
;     reader);
;   * `fn-smid-record-plan' OBSERVATION: the record's protected bytes for
;     `init' and `store rebind-filesystem' (io.lisp
;     `fnn-record-filesystem-identity');
;   * `fn-smid-start-verdict' RECORD OBSERVATION: the owner's start
;     (host/native/owner.lisp fnn-owner-install, PKT-648);
;   * `fn-smid-refusal-text' VERDICT, `fn-smid-rebind-text',
;     `fn-smid-durability-warning' OBSERVATION: every line the host prints.
;
; Nothing here reads a device, trusts a kernel, or claims the observed
; fields are true: an observation is what the host was told by statfs and
; /proc.  The decision's claim is about those facts.

(in-package "ACL2")
(include-book "frame-trailer")
(local (include-book "arithmetic/top" :dir :system))

(defconst *fn-smid-magic* '(70 78 77 73))          ; "FNMI"
(defconst *fn-smid-version* 1)
(defconst *fn-smid-kind* 1)
; Each field carries a u16 length: the codec's width, not a policy.  Linux
; PATH_MAX is 4096 and a mountinfo line field cannot exceed its line.
(defconst *fn-smid-field-max* 65535)
(defconst *fn-smid-max-payload* (* 5 (+ 2 65535)))
; The work bound on one mountinfo line the host hands over.  A longer line
; makes the observation unobserved (a refusal by name), never a skipped line.
(defconst *fn-smid-mountinfo-line-max* 65536)

(defun fn-smid-record-frame-limit ()
  (declare (xargs :guard t))
  (+ *fn-frame-overhead-octets* *fn-smid-max-payload*))

(defun fn-smid-mountinfo-line-max ()
  (declare (xargs :guard t))
  *fn-smid-mountinfo-line-max*)

; -----------------------------------------------------------------------------
; The identity

(defun fn-smid-fieldp (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (<= (len x) *fn-smid-field-max*)))

(defun fn-smid-identityp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 4)
       (fn-smid-fieldp (nth 0 x))
       (fn-smid-fieldp (nth 1 x))
       (fn-smid-fieldp (nth 2 x))
       (fn-smid-fieldp (nth 3 x))))

; The record: the identity and the store's durability policy (PKT-648, the
; coordinator's decision of 2026-09-27): (0) the store may run on a mount
; that disables durability (a warning), (1) it may not (the owner's start is
; refused by name).  `init' takes it from the configuration
; (`fn-smid-init-policy'); `store rebind-filesystem' can set it.  It
; lives here, beside the identity it is judged against, and not in the
; saved profile, whose frame is the store format (D34).
(defun fn-smid-policyp (x)
  (declare (xargs :guard t))
  (or (equal x '(0)) (equal x '(1))))

(defun fn-smid-recordp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 5)
       (fn-smid-fieldp (nth 0 x))
       (fn-smid-fieldp (nth 1 x))
       (fn-smid-fieldp (nth 2 x))
       (fn-smid-fieldp (nth 3 x))
       (fn-smid-policyp (nth 4 x))))

(defun fn-smid-policy (x) (declare (xargs :guard t)) (and (true-listp x) (nth 4 x)))

(defun fn-smid-fsid (x) (declare (xargs :guard t)) (and (true-listp x) (nth 0 x)))
(defun fn-smid-fstype (x) (declare (xargs :guard t)) (and (true-listp x) (nth 1 x)))
(defun fn-smid-mount (x) (declare (xargs :guard t)) (and (true-listp x) (nth 2 x)))
(defun fn-smid-source (x) (declare (xargs :guard t)) (and (true-listp x) (nth 3 x)))

(defun fn-smid-zero-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (equal (car xs) 0) (fn-smid-zero-octetsp (cdr xs)))
    t))

(defun fn-smid-same-filesystemp (recorded observed)
  (declare (xargs :guard t))
  (and (equal (fn-smid-fstype recorded) (fn-smid-fstype observed))
       (if (or (fn-smid-zero-octetsp (fn-smid-fsid recorded))
               (fn-smid-zero-octetsp (fn-smid-fsid observed)))
           (and (equal (fn-smid-mount recorded) (fn-smid-mount observed))
                (equal (fn-smid-source recorded) (fn-smid-source observed)))
         (equal (fn-smid-fsid recorded) (fn-smid-fsid observed)))))

; -----------------------------------------------------------------------------
; The record codec: an FN frame (magic FNMI, version 1, kind 1) whose
; payload is the four fields, each a u16 big-endian length and its octets.

(defun fn-smid-field-encode (x)
  (declare (xargs :guard (fn-smid-fieldp x)))
  (list* (floor (len x) 256) (mod (len x) 256) x))

(defun fn-smid-payload (id)
  (declare (xargs :guard (fn-smid-recordp id)))
  (append (fn-smid-field-encode (nth 0 id))
          (fn-smid-field-encode (nth 1 id))
          (fn-smid-field-encode (nth 2 id))
          (fn-smid-field-encode (nth 3 id))
          (fn-smid-field-encode (nth 4 id))))

(defun fn-smid-field-decode (octets)
  ; (FIELD . REST), or NIL.
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (if (and (consp octets) (consp (cdr octets)))
      (let ((n (+ (* 256 (nfix (car octets))) (nfix (cadr octets))))
            (rest (cddr octets)))
        (if (<= n (len rest))
            (cons (take n rest) (nthcdr n rest))
          nil))
    nil))

;; The rest a field decode leaves is still octets (payload-decode's guard).
(local
 (defthm fn-smid-octet-listp-nthcdr
   (implies (fn-cbor-octet-listp x)
            (fn-cbor-octet-listp (nthcdr n x)))))

(defthm fn-smid-field-decode-rest-octets
  (implies (and (fn-cbor-octet-listp octets)
                (consp (fn-smid-field-decode octets)))
           (fn-cbor-octet-listp (cdr (fn-smid-field-decode octets)))))

(defun fn-smid-payload-decode (octets)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-smid-field-decode)))))
  (if (not (fn-cbor-octet-listp octets))
      nil
    (let* ((a (fn-smid-field-decode octets))
           (b (and (consp a) (fn-smid-field-decode (cdr a))))
           (c (and (consp b) (fn-smid-field-decode (cdr b))))
           (d (and (consp c) (fn-smid-field-decode (cdr c))))
           (e (and (consp d) (fn-smid-field-decode (cdr d)))))
      (if (and (consp e) (null (cdr e)))
          (list (car a) (car b) (car c) (car d) (car e))
        nil))))

(defun fn-smid-record-protected (id)
  ; The protected prefix of the record; the host appends ACL2's trailer
  ; (io.lisp fnn-seal, books/frame-trailer.lisp fn-frame-trailer).
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-smid-recordp id)
      (fn-frame-protected *fn-smid-magic* *fn-smid-version* *fn-smid-kind*
                          (fn-smid-payload id))
    nil))

(defun fn-smid-record-decode (octets digest)
  ; The host passes the file's octets and the trailer ACL2 computes over its
  ; protected prefix (io.lisp fnn-digest-of).  The identity, or NIL.
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest *fn-smid-max-payload*)))
    (if (and (fn-frame-result-okp frame)
             (equal (fn-frame-result-magic frame) *fn-smid-magic*)
             (equal (fn-frame-result-version frame) *fn-smid-version*)
             (equal (fn-frame-result-kind frame) *fn-smid-kind*))
        (fn-smid-payload-decode (fn-frame-result-payload frame))
      nil)))

; -----------------------------------------------------------------------------
; Codec facts

(local
 (defthm fn-smid-octet-listp-of-append
   (implies (and (fn-cbor-octet-listp x) (fn-cbor-octet-listp y))
            (fn-cbor-octet-listp (append x y)))))

(local
 (defthm fn-smid-octet-listp-true-list
   (implies (fn-cbor-octet-listp x) (true-listp x))
   :rule-classes :forward-chaining))

(local
 (defthm fn-smid-field-encode-octets
   (implies (fn-smid-fieldp x)
            (fn-cbor-octet-listp (fn-smid-field-encode x)))))

(local
 (defthm fn-smid-len-field-encode
   (equal (len (fn-smid-field-encode x)) (+ 2 (len x)))))

(defthm fn-smid-payload-octets
  (implies (fn-smid-recordp id)
           (fn-cbor-octet-listp (fn-smid-payload id)))
  :hints (("Goal" :in-theory (disable fn-smid-field-encode))))

(local
 (defthm fn-smid-len-append
   (equal (len (append x y)) (+ (len x) (len y)))))

(defthm fn-smid-payload-bound
  (implies (fn-smid-recordp id)
           (<= (len (fn-smid-payload id)) *fn-smid-max-payload*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-smid-field-encode))))

(verify-guards fn-smid-record-protected)
(verify-guards fn-smid-record-decode)

(local
 (defthm fn-smid-take-of-append-len
   (implies (true-listp x)
            (equal (take (len x) (append x y)) x))))

(local
 (defthm fn-smid-nthcdr-of-append-len
   (equal (nthcdr (len x) (append x y)) y)))

(local
 (defthm fn-smid-u16-split
   (implies (and (natp n) (<= n 65535))
            (equal (+ (* 256 (floor n 256)) (mod n 256)) n))))

(local
 (defthm fn-smid-field-decode-of-encode
   (implies (and (fn-smid-fieldp x) (fn-cbor-octet-listp rest))
            (equal (fn-smid-field-decode (append (fn-smid-field-encode x) rest))
                   (cons x rest)))
   :hints (("Goal" :in-theory (disable floor mod)))))

(local
 (defthm fn-smid-true-listp-field-encode
   (implies (fn-smid-fieldp x) (true-listp (fn-smid-field-encode x)))))

(local
 (defthm fn-smid-field-decode-of-encode-alone
   (implies (fn-smid-fieldp x)
            (equal (fn-smid-field-decode (fn-smid-field-encode x))
                   (cons x nil)))
   :hints (("Goal" :in-theory (disable fn-smid-field-decode-of-encode
                                       fn-smid-field-encode fn-smid-field-decode)
            :use ((:instance fn-smid-field-decode-of-encode (rest nil)))))))

(local
 (defthm fn-smid-field-encode-append-assoc
   (equal (append (fn-smid-field-encode x) rest)
          (list* (floor (len x) 256) (mod (len x) 256) (append x rest)))))

(local
 (defthm fn-smid-list-of-five-nths
   (implies (and (true-listp id) (equal (len id) 5))
            (equal (list (car id) (nth 1 id) (nth 2 id) (nth 3 id) (nth 4 id)) id))
   :hints (("Goal" :expand ((len id) (len (cdr id)) (len (cddr id))
                            (len (cdddr id)) (len (cddddr id))
                            (len (cdr (cddddr id))))))))

(local
 (defthm fn-smid-policyp-is-fieldp
   (implies (fn-smid-policyp x) (fn-smid-fieldp x))))

(defthm fn-smid-payload-decode-of-payload
  (implies (fn-smid-recordp id)
           (equal (fn-smid-payload-decode (fn-smid-payload id)) id))
  :hints (("Goal" :in-theory (e/d (fn-smid-recordp)
                                  (fn-smid-policyp fn-smid-field-encode fn-smid-field-decode
                                   fn-smid-field-encode-append-assoc))
           :expand ((:free (a) (fn-smid-payload-decode a))))))

;; frame-trailer.lisp's local fact, restated for this book.
(local
 (defthm fn-smid-frame-protected-is-octets
   (implies (and (fn-frame-magicp magic)
                 (fn-cbor-octetp version)
                 (fn-cbor-octetp kind)
                 (fn-cbor-octet-listp payload)
                 (<= (len payload) *fn-cbor-max-uint*))
            (fn-cbor-octet-listp (fn-frame-protected magic version kind payload)))
   :hints (("Goal" :in-theory (e/d (fn-frame-protected fn-frame-header-octets)
                                   (fn-frame-header))))))

; KEYSTONE (the record's round trip through the host).  The host writes
; `fnn-seal' of the protected prefix: the prefix and ACL2's trailer over it;
; the open reads the file and hands back its octets and ACL2's trailer over
; its protected prefix.  Those octets decode to the identity recorded.
(defthm fn-smid-record-decode-of-seal
  (implies (fn-smid-recordp id)
           (equal (fn-smid-record-decode
                   (append (fn-smid-record-protected id)
                           (fn-frame-trailer (fn-smid-record-protected id)))
                   (fn-frame-trailer (fn-smid-record-protected id)))
                  id))
  :hints (("Goal" :in-theory (e/d (fn-frame-trailer fn-frame-inputp fn-frame-encode
                                   fn-frame-magicp)
                                  (fn-smid-payload fn-smid-recordp
                                   fn-frame-decode fn-frame-protected))
           :use ((:instance fn-frame-decode-of-encode
                            (magic *fn-smid-magic*) (version *fn-smid-version*)
                            (kind *fn-smid-kind*)
                            (payload (fn-smid-payload id))
                            (max-payload *fn-smid-max-payload*)
                            (digest (fn-frame-digest
                                     (fn-frame-protected
                                      *fn-smid-magic* *fn-smid-version*
                                      *fn-smid-kind* (fn-smid-payload id)))))))))

; -----------------------------------------------------------------------------
; The observation

; (:observed FSID FSTYPE MOUNT SOURCE OPTIONS) or (:unobserved).  OPTIONS
; are the mount's options (per-mount and superblock, comma separated), read
; only for the durability warning.
(defun fn-smid-observationp (obs)
  (declare (xargs :guard t))
  (and (true-listp obs)
       (equal (len obs) 6)
       (equal (nth 0 obs) :observed)
       (fn-smid-fieldp (nth 1 obs))
       (fn-smid-fieldp (nth 2 obs))
       (fn-smid-fieldp (nth 3 obs))
       (fn-smid-fieldp (nth 4 obs))
       (fn-cbor-octet-listp (nth 5 obs))))

(defun fn-smid-observed-identity (obs)
  (declare (xargs :guard t))
  (if (true-listp obs)
      (list (nth 1 obs) (nth 2 obs) (nth 3 obs) (nth 4 obs))
    (list nil nil nil nil)))

(defthm fn-smid-observed-identity-is-identity
  (implies (fn-smid-observationp obs)
           (fn-smid-identityp (fn-smid-observed-identity obs))))

(defun fn-smid-statfs-observation (fsid fstype mount source)
  ; OpenBSD and macOS: statfs names the mount point, type and source.
  (declare (xargs :guard t))
  (if (and (fn-smid-fieldp fsid) (fn-smid-fieldp fstype)
           (fn-smid-fieldp mount) (fn-smid-fieldp source)
           (consp mount))
      (list :observed fsid fstype mount source nil)
    (list :unobserved)))

; --- Linux: /proc/self/mountinfo, one line at a time ------------------------
;
; A line (proc(5)): ID PARENT MAJ:MIN ROOT MOUNT-POINT MOUNT-OPTIONS
; [OPTIONAL...] - FSTYPE SOURCE SUPER-OPTIONS.  Space, tab, newline and
; backslash inside a field are escaped as \ooo.

(defun fn-smid-split-aux (octets cur acc)
  (declare (xargs :guard (and (true-listp octets) (true-listp cur)
                              (true-listp acc))))
  (cond ((endp octets) (reverse (cons (reverse cur) acc)))
        ((equal (car octets) 32)
         (fn-smid-split-aux (cdr octets) nil (cons (reverse cur) acc)))
        (t (fn-smid-split-aux (cdr octets) (cons (car octets) cur) acc))))

(defun fn-smid-split (octets)
  (declare (xargs :guard (true-listp octets)))
  (fn-smid-split-aux octets nil nil))

(defun fn-smid-after-dash (fields)
  (declare (xargs :guard (true-listp fields)))
  (cond ((endp fields) nil)
        ((equal (car fields) '(45)) (cdr fields))
        (t (fn-smid-after-dash (cdr fields)))))

(defun fn-smid-octal-digitp (x)
  (declare (xargs :guard t))
  (and (integerp x) (<= 48 x) (<= x 55)))

(defun fn-smid-unescape-aux (octets acc)
  (declare (xargs :guard (and (true-listp octets) (true-listp acc))
                  :measure (len octets)))
  (cond ((endp octets) (reverse acc))
        ((and (equal (car octets) 92)
              (consp (cdr octets)) (consp (cddr octets)) (consp (cdddr octets))
              (fn-smid-octal-digitp (cadr octets))
              (<= (cadr octets) 51)
              (fn-smid-octal-digitp (caddr octets))
              (fn-smid-octal-digitp (cadddr octets)))
         (fn-smid-unescape-aux (cddddr octets)
                               (cons (+ (* 64 (- (cadr octets) 48))
                                        (* 8 (- (caddr octets) 48))
                                        (- (cadddr octets) 48))
                                     acc)))
        (t (fn-smid-unescape-aux (cdr octets) (cons (car octets) acc)))))

(defun fn-smid-unescape (octets)
  (declare (xargs :guard (true-listp octets)))
  (fn-smid-unescape-aux octets nil))

(defun fn-smid-octet-prefixp (p x)
  (declare (xargs :guard (and (true-listp p) (true-listp x))))
  (cond ((endp p) t)
        ((endp x) nil)
        (t (and (equal (car p) (car x))
                (fn-smid-octet-prefixp (cdr p) (cdr x))))))

; MOUNT contains PATH (both absolute, resolved): MOUNT is "/", or PATH is
; MOUNT, or PATH continues MOUNT with a "/".  "/srv/fn" does not contain
; "/srv/fn-public".
(defun fn-smid-mount-containsp (mount path)
  (declare (xargs :guard (and (true-listp mount) (true-listp path))))
  (or (equal mount '(47))
      (and (consp mount)
           (fn-smid-octet-prefixp mount path)
           (or (equal (len mount) (len path))
               (equal (nth (len mount) path) 47)))))

; An entry: (MOUNT MOUNT-OPTIONS FSTYPE SOURCE SUPER-OPTIONS).
(defun fn-smid-entryp (e)
  (declare (xargs :guard t))
  (and (true-listp e)
       (equal (len e) 5)
       (fn-cbor-octet-listp (nth 0 e))
       (fn-cbor-octet-listp (nth 1 e))
       (fn-cbor-octet-listp (nth 2 e))
       (fn-cbor-octet-listp (nth 3 e))
       (fn-cbor-octet-listp (nth 4 e))))

(defun fn-smid-mountinfo-entry (line)
  (declare (xargs :guard (fn-cbor-octet-listp line)
                  :verify-guards nil))
  (let ((fields (fn-smid-split line)))
    (if (< (len fields) 10)
        nil
      (let ((tail (fn-smid-after-dash (nthcdr 6 fields))))
        (if (< (len tail) 3)
            nil
          (list (fn-smid-unescape (nth 4 fields))
                (nth 5 fields)
                (nth 0 tail) (nth 1 tail) (nth 2 tail)))))))

; The fold state: NIL (no containing mount yet), :OVERLONG (a line exceeded
; the work bound: the observation is refused, never guessed), or the best
; entry so far: the containing mount with the longest mount point, a later
; line winning a tie (a later mount over the same point hides the earlier).
(defun fn-smid-mountinfo-step (best line path)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((equal best :overlong) :overlong)
        ((equal line :overlong) :overlong)
        ((not (and (fn-cbor-octet-listp line) (fn-cbor-octet-listp path)
                   (<= (len line) *fn-smid-mountinfo-line-max*)))
         :overlong)
        (t (let ((e (fn-smid-mountinfo-entry line)))
             (if (and (fn-smid-entryp e)
                      (fn-smid-mount-containsp (nth 0 e) path)
                      (or (not (fn-smid-entryp best))
                          (<= (len (nth 0 best)) (len (nth 0 e)))))
                 e
               best)))))

(defun fn-smid-linux-observation (fsid best)
  (declare (xargs :guard t))
  (if (and (fn-smid-entryp best)
           (fn-smid-fieldp fsid)
           (fn-smid-fieldp (nth 2 best))
           (fn-smid-fieldp (nth 0 best))
           (fn-smid-fieldp (nth 3 best))
           (consp (nth 0 best)))
      (list :observed fsid (nth 2 best) (nth 0 best) (nth 3 best)
            (append (nth 1 best) (cons 44 (nth 4 best))))
    (list :unobserved)))

; -----------------------------------------------------------------------------
; Guards and the selection's invariant

(local
 (defthm fn-smid-octet-listp-of-revappend
   (implies (and (fn-cbor-octet-listp x) (fn-cbor-octet-listp y))
            (fn-cbor-octet-listp (revappend x y)))))

(local
 (defthm fn-smid-octet-listp-of-reverse
   (implies (fn-cbor-octet-listp x)
            (fn-cbor-octet-listp (reverse x)))))

(local
 (defun fn-smid-octet-list-listp (xs)
   (if (consp xs)
       (and (fn-cbor-octet-listp (car xs)) (fn-smid-octet-list-listp (cdr xs)))
     (null xs))))

(local
 (defthm fn-smid-octet-list-listp-of-revappend
   (implies (and (fn-smid-octet-list-listp x) (fn-smid-octet-list-listp y))
            (fn-smid-octet-list-listp (revappend x y)))))

(local
 (defthm fn-smid-split-aux-octets
   (implies (and (fn-cbor-octet-listp octets) (fn-cbor-octet-listp cur)
                 (fn-smid-octet-list-listp acc))
            (fn-smid-octet-list-listp (fn-smid-split-aux octets cur acc)))))

(local
 (defthm fn-smid-octet-list-listp-nth
   (implies (fn-smid-octet-list-listp xs)
            (fn-cbor-octet-listp (nth n xs)))))

(local
 (defthm fn-smid-octet-list-listp-nthcdr
   (implies (fn-smid-octet-list-listp xs)
            (fn-smid-octet-list-listp (nthcdr n xs)))))

(local
 (defthm fn-smid-octet-list-listp-after-dash
   (implies (fn-smid-octet-list-listp xs)
            (fn-smid-octet-list-listp (fn-smid-after-dash xs)))))

(local
 (defthm fn-smid-octet-list-listp-true-listp
   (implies (fn-smid-octet-list-listp xs) (true-listp xs))
   :rule-classes :forward-chaining))

(local
 (defthm fn-smid-unescape-aux-octets
   (implies (and (fn-cbor-octet-listp octets) (fn-cbor-octet-listp acc))
            (fn-cbor-octet-listp (fn-smid-unescape-aux octets acc)))))

(verify-guards fn-smid-mountinfo-entry)

(local
 (defthm fn-smid-octet-list-listp-car
   (implies (fn-smid-octet-list-listp xs)
            (fn-cbor-octet-listp (car xs)))))

(local
 (defthm fn-smid-split-octets
   (implies (fn-cbor-octet-listp line)
            (fn-smid-octet-list-listp (fn-smid-split line)))))

(defthm fn-smid-mountinfo-entry-is-entry
  (implies (and (fn-cbor-octet-listp line)
                (fn-smid-mountinfo-entry line))
           (fn-smid-entryp (fn-smid-mountinfo-entry line)))
  :hints (("Goal" :in-theory (disable fn-smid-split fn-smid-split-aux
                                      fn-smid-after-dash fn-smid-unescape-aux))))

(verify-guards fn-smid-mountinfo-step
  :hints (("Goal" :in-theory (disable fn-smid-mountinfo-entry
                                      fn-smid-mount-containsp))))

; KEYSTONE (the selection).  Whatever the fold chose contains the path:
; the mount point it reports is one the store root actually sits under, so
; a root whose own mount is missing reports the mount underneath it.
(defun fn-smid-best-okp (best path)
  (declare (xargs :guard t))
  (or (null best)
      (equal best :overlong)
      (and (fn-smid-entryp best)
           (true-listp path)
           (fn-smid-mount-containsp (nth 0 best) path))))

(defthm fn-smid-mountinfo-step-preserves-best-okp
  (implies (fn-smid-best-okp best path)
           (fn-smid-best-okp (fn-smid-mountinfo-step best line path) path))
  :hints (("Goal" :in-theory (disable fn-smid-mountinfo-entry
                                      fn-smid-mount-containsp))))

; -----------------------------------------------------------------------------
; The durability policy (PKT-648)
;
; Observable here: an `nobarrier' or `barrier=0' mount option (ext3, ext4 and
; older XFS print it among the mount's options) and a memory filesystem
; (tmpfs, ramfs).  NOT observable here: ZFS `sync=disabled', a dataset
; property that neither statfs nor mountinfo carries, and a drive's volatile
; write cache.  Those remain the operator's obligation (docs/operator.md,
; Storage requirements).

(defun fn-smid-comma-split-aux (octets cur acc)
  (declare (xargs :guard (and (true-listp cur) (true-listp acc))))
  (cond ((atom octets) (reverse (cons (reverse cur) acc)))
        ((equal (car octets) 44)
         (fn-smid-comma-split-aux (cdr octets) nil (cons (reverse cur) acc)))
        (t (fn-smid-comma-split-aux (cdr octets) (cons (car octets) cur) acc))))

(defthm fn-smid-true-listp-comma-split-aux
  (implies (true-listp acc) (true-listp (fn-smid-comma-split-aux octets cur acc)))
  :rule-classes :type-prescription)

(defun fn-smid-unsafe-reason (observation)
  ; :NOBARRIER, :MEMORY, or NIL when nothing observable disables durability.
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-smid-observationp)))))
  (if (not (fn-smid-observationp observation))
      nil
    (let ((options (fn-smid-comma-split-aux (nth 5 observation) nil nil))
          (fstype (nth 2 observation)))
      (cond ((or (member-equal (list 110 111 98 97 114 114 105 101 114) options) ; nobarrier
                 (member-equal (list 98 97 114 114 105 101 114 61 48) options))   ; barrier=0
             :nobarrier)
            ((or (equal fstype (list 116 109 112 102 115))    ; tmpfs
                 (equal fstype (list 114 97 109 102 115)))    ; ramfs
             :memory)
            (t nil)))))

(defun fn-smid-policy-octets (policy)
  (declare (xargs :guard t))
  (if (equal policy 1) (list 1) (list 0)))

; The policy `init' (and `store import') records: 1 for a store made under
; a mission's fn.toml (`[ops] mission', the release and public node's
; configuration: docs/install.md, tools/runbooks/public-node), 0 otherwise
; (the development, default and scale presets tests and benchmarks run on
; tmpfs with).  MISSION is the configuration's mission name, or NIL.
; `store rebind-filesystem --storage-require-durable on|off' changes it.
(defun fn-smid-init-policy (mission)
  (declare (xargs :guard t))
  (if mission 1 0))

; -----------------------------------------------------------------------------
; The open's decision

(defun fn-smid-observed-record (observation policy)
  (declare (xargs :guard t))
  (append (fn-smid-observed-identity observation)
          (list (fn-smid-policy-octets policy))))

; RECORD: (:absent), or (:present OCTETS DIGEST) where DIGEST is ACL2's
; trailer over OCTETS' protected prefix.
(defun fn-smid-open-verdict (record observation)
  (declare (xargs :guard t))
  (cond ((not (fn-smid-observationp observation))
         (list :refused :filesystem-unobserved))
        ((not (and (true-listp record) (equal (len record) 3)
                   (equal (car record) :present)))
         (list :refused :filesystem-unrecorded
               (fn-smid-observed-identity observation)))
        (t (let ((recorded (fn-smid-record-decode (nth 1 record) (nth 2 record))))
             (cond ((not (fn-smid-recordp recorded))
                    (list :refused :filesystem-record-invalid
                          (fn-smid-observed-identity observation)))
                   ((fn-smid-same-filesystemp
                     recorded (fn-smid-observed-identity observation))
                    (list :open))
                   (t (list :refused :filesystem-changed recorded
                            (fn-smid-observed-identity observation))))))))

; The owner's start (host/native/owner.lisp fnn-owner-install): the open's
; decision, then the policy against the observed mount.
(defun fn-smid-start-verdict (record observation)
  (declare (xargs :guard t))
  (let ((verdict (fn-smid-open-verdict record observation)))
    (cond ((not (equal verdict (list :open))) verdict)
          ((and (equal (fn-smid-policy (fn-smid-record-decode (nth 1 record)
                                                               (nth 2 record)))
                       (list 1))
                (fn-smid-unsafe-reason observation))
           (list :refused :storage-not-durable
                 (fn-smid-unsafe-reason observation)
                 (fn-smid-observed-identity observation)))
          (t (list :start)))))

; The record `init' writes: the protected prefix of the observed identity
; under POLICY (0 or 1).
(defun fn-smid-record-plan (observation policy)
  (declare (xargs :guard t))
  (if (fn-smid-observationp observation)
      (list :record (fn-smid-record-protected
                     (fn-smid-observed-record observation policy)))
    (list :refused :filesystem-unobserved)))

; `store rebind-filesystem': the observed identity under REQUESTED (0 or 1),
; else the policy of the record it replaces, else 1.
(defun fn-smid-rebind-policy (record requested)
  (declare (xargs :guard t :verify-guards nil))
  (let ((old (and (true-listp record) (equal (len record) 3)
                  (equal (car record) :present)
                  (fn-smid-record-decode (nth 1 record) (nth 2 record)))))
    (cond ((or (equal requested 0) (equal requested 1)) requested)
          ((and (fn-smid-recordp old) (equal (nth 4 old) (list 0))) 0)
          (t 1))))

(verify-guards fn-smid-rebind-policy)

(defun fn-smid-rebind-plan (record observation requested)
  (declare (xargs :guard t))
  (fn-smid-record-plan observation (fn-smid-rebind-policy record requested)))

(defun fn-smid-sealed (protected)
  ; What the host writes for PROTECTED (io.lisp fnn-seal), and the record
  ; observation the open then reads back.
  (declare (xargs :guard t))
  (list :present
        (append (true-list-fix protected) (fn-frame-trailer protected))
        (fn-frame-trailer protected)))

(defthm fn-smid-observed-record-is-record
  (implies (fn-smid-observationp obs)
           (fn-smid-recordp (fn-smid-observed-record obs policy))))

(local (in-theory (disable fn-smid-record-decode fn-smid-record-protected
                           fn-smid-recordp fn-smid-observed-identity
                           fn-smid-same-filesystemp)))

(local
 (defthm fn-smid-true-listp-record-protected
   (true-listp (fn-smid-record-protected id))
   :hints (("Goal" :in-theory (e/d (fn-smid-record-protected)
                                   (fn-frame-protected fn-smid-payload))
            :use ((:instance fn-smid-frame-protected-is-octets
                             (magic *fn-smid-magic*) (version *fn-smid-version*)
                             (kind *fn-smid-kind*)
                             (payload (fn-smid-payload id))))))))

(local
 (defthm fn-smid-true-list-fix-when-true-listp
   (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn-smid-true-list-fix-record-protected
   (equal (true-list-fix (fn-smid-record-protected id))
          (fn-smid-record-protected id))
   :hints (("Goal" :use fn-smid-true-listp-record-protected
            :in-theory (disable fn-smid-true-listp-record-protected)))))

; The recorded identity is the observed one: the policy field is not
; compared.
(local
 (defthm fn-smid-same-filesystemp-of-observed-record
   (implies (fn-smid-observationp obs)
            (equal (fn-smid-same-filesystemp (fn-smid-observed-record obs policy) x)
                   (fn-smid-same-filesystemp (fn-smid-observed-identity obs) x)))
   :hints (("Goal" :in-theory (enable fn-smid-same-filesystemp
                                      fn-smid-observed-identity)))))

(local
 (defthm fn-smid-policy-of-observed-record
   (implies (fn-smid-observationp obs)
            (equal (fn-smid-policy (fn-smid-observed-record obs policy))
                   (fn-smid-policy-octets policy)))
   :hints (("Goal" :in-theory (enable fn-smid-observed-identity)))))

(local (in-theory (disable fn-smid-observationp fn-smid-observed-record
                           fn-smid-unsafe-reason)))

; KEYSTONE (init or rebind, then open).  A store whose record was written
; from observation OBS (the plan answers :record only for an observation, so
; OBS needs no hypothesis of its own) opens under a later observation OBS2
; exactly when the two name the same filesystem, whatever its policy.
(defthm fn-smid-recorded-store-opens-iff-same-filesystem
  (implies (and (fn-smid-observationp obs2)
                (equal (fn-smid-record-plan obs policy) (list :record protected)))
           (equal (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs2)
                         (list :open))
                  (fn-smid-same-filesystemp (fn-smid-observed-identity obs)
                                            (fn-smid-observed-identity obs2)))))

(local
 (defthm fn-smid-mount-of-observed-identity
   (implies (fn-smid-observationp obs)
            (equal (nth 2 (fn-smid-observed-identity obs))
                   (nth 3 obs)))
   :hints (("Goal" :in-theory (enable fn-smid-observed-identity
                                      fn-smid-observationp)))))

(local
 (defthm fn-smid-mount-of-observed-record
   (implies (fn-smid-observationp obs)
            (equal (nth 2 (fn-smid-observed-record obs policy))
                   (nth 3 obs)))
   :hints (("Goal" :in-theory (enable fn-smid-observed-record
                                      fn-smid-observed-identity
                                      fn-smid-observationp)))))

;; The recorded identity's fields are the observation's.
(local
 (defthm fn-smid-fields-of-observed-record
   (implies (fn-smid-observationp obs)
            (and (equal (fn-smid-fsid (fn-smid-observed-record obs policy))
                        (fn-smid-fsid (fn-smid-observed-identity obs)))
                 (equal (fn-smid-fstype (fn-smid-observed-record obs policy))
                        (fn-smid-fstype (fn-smid-observed-identity obs)))
                 (equal (fn-smid-mount (fn-smid-observed-record obs policy))
                        (fn-smid-mount (fn-smid-observed-identity obs)))
                 (equal (fn-smid-source (fn-smid-observed-record obs policy))
                        (fn-smid-source (fn-smid-observed-identity obs)))))
   :hints (("Goal" :in-theory (enable fn-smid-observed-record
                                      fn-smid-observed-identity
                                      fn-smid-observationp)))))

; KEYSTONE (PKT-706, the sandboxed view).  A store recorded from observation
; OBS opens under OBS2 whenever both report the same nonzero fsid and the
; same type, whatever mount point and source OBS2 shows: the shipped unit's
; ReadWritePaths bind view of /var/lib/fn, recorded as `/' by an `init' or a
; `store rebind-filesystem' run outside the unit, opens inside it.
(defthm fn-smid-same-fsid-view-opens
  (implies (and (fn-smid-observationp obs2)
                (equal (fn-smid-record-plan obs policy) (list :record protected))
                (equal (fn-smid-fstype (fn-smid-observed-identity obs))
                       (fn-smid-fstype (fn-smid-observed-identity obs2)))
                (equal (fn-smid-fsid (fn-smid-observed-identity obs))
                       (fn-smid-fsid (fn-smid-observed-identity obs2)))
                (not (fn-smid-zero-octetsp
                      (fn-smid-fsid (fn-smid-observed-identity obs2)))))
           (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs2)
                  (list :open)))
  :hints (("Goal" :in-theory (e/d (fn-smid-same-filesystemp)
                                  (fn-smid-fsid fn-smid-fstype
                                   fn-smid-mount fn-smid-source))
           :use ((:instance fn-smid-recorded-store-opens-iff-same-filesystem)))))

; KEYSTONE (the missing mount, another filesystem).  When the store root now
; resolves onto another filesystem (its volume unmounted and the directory
; underneath visible: another fsid, or, where an fsid is not reported,
; another mount point or source), the open is refused by name with both
; identities.
(defthm fn-smid-other-filesystem-is-refused-by-name
  (implies (and (fn-smid-observationp obs2)
                (equal (fn-smid-record-plan obs policy) (list :record protected))
                (not (fn-smid-same-filesystemp (fn-smid-observed-identity obs)
                                               (fn-smid-observed-identity obs2))))
           (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs2)
                  (list :refused :filesystem-changed
                        (fn-smid-observed-record obs policy)
                        (fn-smid-observed-identity obs2)))))

; KEYSTONE (the missing mount where the fsid is known).  Known fsids that
; differ are refused by name, whatever the mount point shows.
(defthm fn-smid-other-fsid-is-refused-by-name
  (implies (and (fn-smid-observationp obs2)
                (equal (fn-smid-record-plan obs policy) (list :record protected))
                (not (fn-smid-zero-octetsp
                      (fn-smid-fsid (fn-smid-observed-identity obs))))
                (not (fn-smid-zero-octetsp
                      (fn-smid-fsid (fn-smid-observed-identity obs2))))
                (not (equal (fn-smid-fsid (fn-smid-observed-identity obs))
                            (fn-smid-fsid (fn-smid-observed-identity obs2)))))
           (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs2)
                  (list :refused :filesystem-changed
                        (fn-smid-observed-record obs policy)
                        (fn-smid-observed-identity obs2))))
  :hints (("Goal" :in-theory (e/d (fn-smid-same-filesystemp)
                                  (fn-smid-fsid fn-smid-fstype
                                   fn-smid-mount fn-smid-source))
           :use ((:instance fn-smid-other-filesystem-is-refused-by-name)))))

; KEYSTONE (where no fsid is reported, the mount point still decides).  An
; unreported fsid (OpenBSD's unprivileged zeros, Linux tmpfs before 6.7)
; falls back to mount point and source: another mount point is refused.
(defthm fn-smid-unreported-fsid-moved-mount-is-refused-by-name
  (implies (and (fn-smid-observationp obs2)
                (equal (fn-smid-record-plan obs policy) (list :record protected))
                (fn-smid-zero-octetsp
                 (fn-smid-fsid (fn-smid-observed-identity obs2)))
                (not (equal (fn-smid-mount (fn-smid-observed-identity obs))
                            (fn-smid-mount (fn-smid-observed-identity obs2)))))
           (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs2)
                  (list :refused :filesystem-changed
                        (fn-smid-observed-record obs policy)
                        (fn-smid-observed-identity obs2))))
  :hints (("Goal" :in-theory (e/d (fn-smid-same-filesystemp)
                                  (fn-smid-fsid fn-smid-fstype
                                   fn-smid-mount fn-smid-source))
           :use ((:instance fn-smid-other-filesystem-is-refused-by-name)))))

; KEYSTONE (no record, no open).  A store root with no record is never
; opened: not by a first sight of its filesystem, not by any observation.
(defthm fn-smid-absent-record-is-refused
  (equal (fn-smid-open-verdict (list :absent) obs)
         (if (fn-smid-observationp obs)
             (list :refused :filesystem-unrecorded (fn-smid-observed-identity obs))
           (list :refused :filesystem-unobserved))))

(defthm fn-smid-open-verdict-opens-only-on-a-match
  (implies (equal (fn-smid-open-verdict record obs) (list :open))
           (and (fn-smid-observationp obs)
                (equal (car record) :present)
                (fn-smid-recordp (fn-smid-record-decode (nth 1 record)
                                                        (nth 2 record)))
                (fn-smid-same-filesystemp
                 (fn-smid-record-decode (nth 1 record) (nth 2 record))
                 (fn-smid-observed-identity obs)))))

; KEYSTONE (PKT-648, the start).  On the filesystem it was recorded on, a
; store's owner start is refused by name exactly when its policy requires
; durability and the mount observably disables it; otherwise it starts.
(defthm fn-smid-start-refused-iff-required-and-unsafe
  (implies (and (fn-smid-observationp obs2)
                (equal (fn-smid-record-plan obs policy) (list :record protected))
                (fn-smid-same-filesystemp (fn-smid-observed-identity obs)
                                          (fn-smid-observed-identity obs2)))
           (equal (fn-smid-start-verdict (fn-smid-sealed protected) obs2)
                  (if (and (equal policy 1) (fn-smid-unsafe-reason obs2))
                      (list :refused :storage-not-durable
                            (fn-smid-unsafe-reason obs2)
                            (fn-smid-observed-identity obs2))
                    (list :start)))))

(local
 (defthm fn-smid-record-plan-needs-an-observation
   (implies (not (fn-smid-observationp obs))
            (not (equal (fn-smid-record-plan obs policy) (list :record protected))))))

(local
 (defthm fn-smid-same-filesystemp-reflexive
   (fn-smid-same-filesystemp x x)
   :hints (("Goal" :in-theory (enable fn-smid-same-filesystemp)))))

; KEYSTONE (rebind).  After `store rebind-filesystem' under an observation,
; an open under the same observation opens.  (The plan answers :record only
; for an observation, so none is assumed.)
(defthm fn-smid-rebound-store-opens
  (implies (equal (fn-smid-rebind-plan record obs requested)
                  (list :record protected))
           (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs)
                  (list :open)))
  :hints (("Goal" :in-theory (disable fn-smid-rebind-policy fn-smid-record-plan
                                      fn-smid-open-verdict fn-smid-sealed
                                      fn-smid-recorded-store-opens-iff-same-filesystem)
           :use ((:instance fn-smid-recorded-store-opens-iff-same-filesystem
                            (obs2 obs)
                            (policy (fn-smid-rebind-policy record requested)))))))

;; KEYSTONE (PKT-706, the cure).  `store rebind-filesystem' run where the
;; operator is (outside the unit, observation OBS) cures the open the unit's
;; namespace makes (OBS2) whenever the two see one filesystem by its fsid:
;; the remedy the refusal names is one that works.
(defthm fn-smid-rebind-outside-opens-inside
  (implies (and (equal (fn-smid-rebind-plan record obs requested)
                       (list :record protected))
                (fn-smid-observationp obs2)
                (equal (fn-smid-fstype (fn-smid-observed-identity obs))
                       (fn-smid-fstype (fn-smid-observed-identity obs2)))
                (equal (fn-smid-fsid (fn-smid-observed-identity obs))
                       (fn-smid-fsid (fn-smid-observed-identity obs2)))
                (not (fn-smid-zero-octetsp
                      (fn-smid-fsid (fn-smid-observed-identity obs2)))))
           (equal (fn-smid-open-verdict (fn-smid-sealed protected) obs2)
                  (list :open)))
  :hints (("Goal" :in-theory (disable fn-smid-rebind-policy fn-smid-record-plan
                                      fn-smid-open-verdict fn-smid-sealed
                                      fn-smid-fsid fn-smid-fstype
                                      fn-smid-same-fsid-view-opens)
           :use ((:instance fn-smid-same-fsid-view-opens
                            (policy (fn-smid-rebind-policy record requested)))))))

; -----------------------------------------------------------------------------
; The open the host calls: a store made before the record

; Every store made before 2026-09-27 (and a store whose `init' died before
; its record) has a complete root and no record.  An offline open of such a
; store proceeds with a warning naming the remedy (`store rebind-filesystem');
; its owner's START is refused (`fn-smid-start-verdict' above is strict), so
; no node serves a store whose filesystem is not required.  A root with no
; record and no config.json (the empty directory underneath a missing
; volume) is refused at every open.  CONFIGURED is the host's observation
; that config.json is present as a regular file.
(defun fn-smid-open-decision (record observation configured)
  (declare (xargs :guard t))
  (if (and (equal record (list :absent)) configured
           (fn-smid-observationp observation))
      (list :open-unrecorded (fn-smid-observed-identity observation))
    (fn-smid-open-verdict record observation)))

; KEYSTONE (the host's open is the verdict).  Wherever a record is present,
; or the root holds no configuration, the host's open decision is
; `fn-smid-open-verdict', so every keystone above is about it.
(defthm fn-smid-open-decision-is-the-verdict
  (implies (or (not (equal record (list :absent))) (not configured))
           (equal (fn-smid-open-decision record observation configured)
                  (fn-smid-open-verdict record observation))))

; KEYSTONE (the missing volume, the empty directory).  No record and no
; configuration: refused by name, whatever is observed.
(defthm fn-smid-empty-root-is-refused
  (implies (not configured)
           (equal (car (fn-smid-open-decision (list :absent) observation configured))
                  :refused)))

; KEYSTONE (a store made before the record is never started).
(defthm fn-smid-unrecorded-store-never-starts
  (not (equal (fn-smid-start-verdict (list :absent) observation) (list :start))))

; -----------------------------------------------------------------------------
; Text: every line the host prints for this boundary

(defun fn-smid-codes (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      nil
    (cons (char-code (car chars)) (fn-smid-codes (cdr chars)))))

(defun fn-smid-text (s)
  (declare (xargs :guard (stringp s)))
  (fn-smid-codes (coerce s 'list)))

(defun fn-smid-hex-digit (n)
  (declare (xargs :guard t))
  (let ((n (nfix n)))
    (if (< n 10) (+ 48 n) (+ 87 n))))

(defun fn-smid-hex-aux (octets acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp octets)
      (fn-smid-hex-aux (cdr octets)
                       (list* (fn-smid-hex-digit (mod (nfix (car octets)) 16))
                              (fn-smid-hex-digit (floor (nfix (car octets)) 16))
                              acc))
    (reverse acc)))

(defthm fn-smid-true-listp-hex-aux
  (implies (true-listp acc) (true-listp (fn-smid-hex-aux octets acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable floor mod fn-smid-hex-digit))))

(defun fn-smid-hex (octets)
  (declare (xargs :guard t))
  (fn-smid-hex-aux octets nil))

; A field as the operator reads it: printable ASCII as itself, anything else
; (and the backslash) as \xHH, so the line is exact and one line.
(defun fn-smid-display-aux (octets acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp octets)
      (let ((b (nfix (car octets))))
        (fn-smid-display-aux
         (cdr octets)
         (if (and (<= 32 b) (<= b 126) (not (equal b 92)))
             (cons b acc)
           (list* (fn-smid-hex-digit (mod b 16))
                  (fn-smid-hex-digit (floor (mod b 256) 16))
                  120 92 acc))))
    (reverse acc)))

(defthm fn-smid-true-listp-display-aux
  (implies (true-listp acc) (true-listp (fn-smid-display-aux octets acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable floor mod fn-smid-hex-digit))))

(defun fn-smid-display (octets)
  (declare (xargs :guard t))
  (fn-smid-display-aux octets nil))

(defun fn-smid-describe (id)
  (declare (xargs :guard t))
  (append (fn-smid-display (fn-smid-fstype id))
          (fn-smid-text " at ")
          (fn-smid-display (fn-smid-mount id))
          (fn-smid-text " from ")
          (fn-smid-display (fn-smid-source id))
          (if (fn-smid-zero-octetsp (fn-smid-fsid id))
              (fn-smid-text " (fsid not reported)")
            (append (fn-smid-text " (fsid ")
                    (fn-smid-hex (fn-smid-fsid id))
                    (fn-smid-text ")")))))

; The reason as the operator reads it.
(defun fn-smid-unsafe-text (reason)
  (declare (xargs :guard t))
  (if (equal reason :nobarrier)
      (fn-smid-text "is mounted without write barriers (nobarrier or barrier=0): an acknowledged article can be lost at power loss")
    (fn-smid-text "is held in memory (tmpfs or ramfs): every article is lost at power loss or reboot")))

(defun fn-smid-refusal-text (verdict)
  ; NIL exactly for (:open); otherwise the refusal line the host prints.
  (declare (xargs :guard t))
  (cond ((not (and (true-listp verdict) (equal (car verdict) :refused)))
         nil)
        ((equal (nth 1 verdict) :filesystem-changed)
         (append (fn-smid-text "store filesystem changed: expected ")
                 (fn-smid-describe (nth 2 verdict))
                 (fn-smid-text ", found ")
                 (fn-smid-describe (nth 3 verdict))
                 (fn-smid-text "; mount the node volume or run `store rebind-filesystem` after moving the store deliberately")))
        ((equal (nth 1 verdict) :filesystem-unrecorded)
         (append (fn-smid-text "store filesystem unrecorded: the store holds no filesystem identity record (found ")
                 (fn-smid-describe (nth 2 verdict))
                 (fn-smid-text "); mount the node volume if it is missing, run init again if it was interrupted, or run `store rebind-filesystem` for a store moved deliberately or made before the record")))
        ((equal (nth 1 verdict) :storage-not-durable)
         (append (fn-smid-text "start refused: store filesystem ")
                 (fn-smid-describe (nth 3 verdict))
                 (fn-smid-text " ")
                 (fn-smid-unsafe-text (nth 2 verdict))
                 (fn-smid-text "; this store requires durable storage (storage-require-durable): move it to a durable mount, or run `store rebind-filesystem --storage-require-durable off` to accept the risk (docs/operator.md, Storage requirements)")))
        ((equal (nth 1 verdict) :filesystem-record-invalid)
         (append (fn-smid-text "store filesystem record invalid: filesystem-identity.fnmi does not decode (found ")
                 (fn-smid-describe (nth 2 verdict))
                 (fn-smid-text "); check that the node volume is mounted, then run `store rebind-filesystem`")))
        (t (fn-smid-text "store filesystem unobserved: the filesystem under the store root could not be observed; the store is not opened"))))

; The host prints a refusal exactly when the open did not answer (:open),
; and the start exactly when it did not answer (:start).
(defthm fn-smid-refusal-text-is-nil-exactly-for-open
  (iff (fn-smid-refusal-text (fn-smid-open-verdict record obs))
       (not (equal (fn-smid-open-verdict record obs) (list :open))))
  :hints (("Goal" :in-theory (disable fn-smid-describe fn-smid-text
                                      fn-smid-record-decode
                                      fn-smid-same-filesystemp
                                      fn-smid-observationp))))

(defthm fn-smid-refusal-text-is-nil-exactly-for-start
  (iff (fn-smid-refusal-text (fn-smid-start-verdict record obs))
       (not (equal (fn-smid-start-verdict record obs) (list :start))))
  :hints (("Goal" :in-theory (disable fn-smid-describe fn-smid-text
                                      fn-smid-unsafe-text
                                      fn-smid-record-decode
                                      fn-smid-same-filesystemp
                                      fn-smid-observationp))))

; `store rebind-filesystem': the line naming what was recorded and what it
; replaced (RECORD is the open's record observation before the rebind).
(defun fn-smid-rebind-text (record observation requested)
  (declare (xargs :guard t :verify-guards nil))
  (let ((old (and (true-listp record) (equal (len record) 3)
                  (equal (car record) :present)
                  (fn-smid-record-decode (nth 1 record) (nth 2 record)))))
    (append (fn-smid-text "rebound store filesystem: ")
            (fn-smid-describe (fn-smid-observed-identity observation))
            (if (equal (fn-smid-rebind-policy record requested) 1)
                (fn-smid-text " storage-require-durable=on")
              (fn-smid-text " storage-require-durable=off"))
            (if (fn-smid-recordp old)
                (append (fn-smid-text "; was ") (fn-smid-describe old)
                        (if (equal (nth 4 old) (list 1))
                            (fn-smid-text " storage-require-durable=on")
                          (fn-smid-text " storage-require-durable=off")))
              (fn-smid-text "; no valid record before")))))

(verify-guards fn-smid-rebind-text)

;; An offline open of a store made before the record.
(defun fn-smid-unrecorded-warning (decision)
  (declare (xargs :guard t))
  (if (and (true-listp decision) (equal (car decision) :open-unrecorded))
      (append (fn-smid-text "warning: store filesystem unrecorded: this store predates its filesystem record (found ")
              (fn-smid-describe (nth 1 decision))
              (fn-smid-text "); its owner will not start until `store rebind-filesystem` records where it is"))
    nil))

(defthm fn-smid-refusal-text-is-nil-exactly-for-an-open-decision
  (iff (fn-smid-refusal-text (fn-smid-open-decision record obs configured))
       (not (member-equal (car (fn-smid-open-decision record obs configured))
                          (list :open :open-unrecorded))))
  :hints (("Goal" :in-theory (disable fn-smid-describe fn-smid-text
                                      fn-smid-record-decode
                                      fn-smid-same-filesystemp
                                      fn-smid-observationp))))

; PKT-648's warning: printed by the owner's start and by `status' and
; `health' for a store on such a mount, whatever its policy (host/native/
; io.lisp fnn-filesystem-durability-warn).  NIL when the mount shows nothing
; unsafe.
(defun fn-smid-durability-warning (observation)
  (declare (xargs :guard t))
  (let ((reason (fn-smid-unsafe-reason observation)))
    (if (null reason)
        nil
      (append (fn-smid-text "warning: store filesystem ")
              (fn-smid-describe (fn-smid-observed-identity observation))
              (fn-smid-text " ")
              (fn-smid-unsafe-text reason)
              (fn-smid-text " (docs/operator.md, Storage requirements)")))))
