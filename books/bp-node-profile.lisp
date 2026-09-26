; The BP node's profile (PRF-131 part 2; D27; planning/design-2026-09-25-
; bounds.md section 5, P5 for BP).
;
; How many rows a node's FNBS machine holds (received bundles, fragments,
; queued and forwarding jobs) and how many held octets they may total are the
; operator's numbers, not constants.  The profile is a file in the FNBS
; journal root, `bp-node-profile', written by `bp-node profile' and read by
; every BP verb that opens the journal (host/native/bp-service.lisp
; fnn-bps-open).  Its absence is the default profile (64 rows, 16 MiB), which
; is the machine every journal written before this file existed ran under.
;
; What ACL2 fixes is the relation, not the values: each field is a machine
; limit (fn-bpn-machine-limitp, 1 to 2^24), which is the representation
; ceiling of the machine state; every profile that relation admits opens a
; machine (fn-bpnpf-valid-profile-opens), and the file's frame carries every
; value the relation admits (fn-bpnpf-read-of-octets).  A profile is only
; raised: a write that lowers a field below the one in force is refused
; (fn-bpnpf-upgradep), so a journal written under the old profile still fits.
; A journal whose rows exceed the profile it is opened under (the file was
; removed, or copied from elsewhere) is refused at replay with a named
; verdict, :held-beyond-profile (books/bp-fnbs-family-replay.lisp), never
; truncated.
;
; Work bounds stay constants and say so: *fn-bpn-machine-max-records* (4096
; lifecycle records between rotations), the TCPCL segment and transfer MRUs,
; and the ADU (*fn-bpa-max-octets*), bundle decoder (*fn-bpb-max-input*) and
; held-image (*fn-bpnf-max-held-image*) ceilings, which are data caps this
; profile does not yet carry (PKT-276).
(in-package "ACL2")
(include-book "bp-node-machine")
(include-book "frame-invariants")

(defconst *fn-bpnpf-format*
  '(102 110 45 98 112 45 112 114 111 102 105 108 101 45 49)) ; fn-bp-profile-1
(defconst *fn-bpnpf-spec* '(:text :nat :nat))
(defconst *fn-bpnpf-default-rows* *fn-bpn-machine-max-jobs*)
(defconst *fn-bpnpf-default-octets* *fn-bpn-machine-max-octets*)

(defun fn-bpnpf-file-name ()
  (declare (xargs :guard t))
  "bp-node-profile")

; The profile file is one frame of a 15-octet text and two naturals; the
; read bound is a work bound on reading it, not a data cap.
(defun fn-bpnpf-read-bound ()
  (declare (xargs :guard t))
  256)

(defun fn-bpnpf-validp (rows octets)
  (declare (xargs :guard t))
  (and (fn-bpn-machine-limitp rows) (fn-bpn-machine-limitp octets)))

(local
 (defthm fn-bpnpf-limit-is-a-frame-nat
   (implies (fn-bpn-machine-limitp x) (fn-frame-natp x))
   :hints (("Goal" :in-theory (enable fn-frame-natp)))))

(local
 (defthm fn-bpnpf-values-ok
   (implies (fn-bpnpf-validp rows octets)
            (fn-frame-values-okp *fn-bpnpf-spec*
                                 (list *fn-bpnpf-format* rows octets)))
   :hints (("Goal" :in-theory (enable fn-frame-values-okp fn-frame-field-okp)))))

(defun fn-bpnpf-default ()
  (declare (xargs :guard t))
  (list *fn-bpnpf-default-rows* *fn-bpnpf-default-octets*))

(defun fn-bpnpf-rows (p) (declare (xargs :guard t)) (fn-bpn-nth 0 p))
(defun fn-bpnpf-held-octets (p) (declare (xargs :guard t)) (fn-bpn-nth 1 p))

; The file's octets for a valid profile; NIL otherwise.
(defun fn-bpnpf-octets (rows octets)
  (declare (xargs :guard t))
  (if (fn-bpnpf-validp rows octets)
      (fn-frame-fields-octets *fn-bpnpf-spec*
                              (list *fn-bpnpf-format* rows octets))
    nil))

; The profile a journal opens under.  PRESENT is whether the file exists;
; BYTES its octets.  Absent: the default.  Present: (ROWS OCTETS) when the
; octets are exactly one profile frame of a valid profile, else NIL (the
; host refuses to open).
(defun fn-bpnpf-read (present bytes)
  (declare (xargs :guard t))
  (if (not present)
      (fn-bpnpf-default)
    (if (not (fn-cbor-octet-listp bytes))
        nil
      (let ((parsed (fn-frame-fields-parse *fn-bpnpf-spec* bytes)))
        (if (not (fn-frame-parse-okp parsed))
            nil
          (let ((v (fn-frame-parse-value parsed)))
            (if (and (true-listp v) (equal (len v) 3)
                     (equal (car v) *fn-bpnpf-format*)
                     (fn-bpnpf-validp (cadr v) (caddr v)))
                (list (cadr v) (caddr v))
              nil)))))))

; A write is admitted only when it raises or keeps every field of the
; profile in force.
(defun fn-bpnpf-upgradep (old rows octets)
  (declare (xargs :guard t))
  (and (true-listp old) (equal (len old) 2)
       (fn-bpnpf-validp (car old) (cadr old))
       (fn-bpnpf-validp rows octets)
       (<= (car old) rows) (<= (cadr old) octets)))

; The octets `bp-node profile' publishes: NIL (refused) unless the write
; raises or keeps the profile in force.
(defun fn-bpnpf-write-octets (old rows octets)
  (declare (xargs :guard t))
  (if (fn-bpnpf-upgradep old rows octets)
      (fn-bpnpf-octets rows octets)
    nil))

; -----------------------------------------------------------------------------
; Theorems.

(defthm fn-bpnpf-default-is-valid
  (fn-bpnpf-validp (car (fn-bpnpf-default)) (cadr (fn-bpnpf-default))))

; Keystone: a saved profile opens.  The octets written for every profile the
; relation admits read back as exactly that profile, so validation and
; representation agree: no valid profile is one the file cannot carry.
(defthm fn-bpnpf-read-of-octets
  (implies (fn-bpnpf-validp rows octets)
           (equal (fn-bpnpf-read t (fn-bpnpf-octets rows octets))
                  (list rows octets)))
  :hints (("Goal" :in-theory (e/d (fn-bpnpf-octets)
                                  (fn-frame-fields-octets fn-frame-fields-parse
                                   fn-bpnpf-validp))
           :use ((:instance fn-frame-fields-parse-of-octets
                  (specs *fn-bpnpf-spec*)
                  (values (list *fn-bpnpf-format* rows octets)))
                 (:instance fn-frame-fields-octets-are-octets
                  (specs *fn-bpnpf-spec*)
                  (values (list *fn-bpnpf-format* rows octets)))))))

; What the node reads is always a valid profile or a refusal.
(defthm fn-bpnpf-read-is-valid
  (let ((p (fn-bpnpf-read present bytes)))
    (implies p
             (and (equal (len p) 2)
                  (fn-bpnpf-validp (car p) (cadr p))))))

; Keystone: every profile the relation admits opens a machine, and that
; machine holds exactly the profile's rows and octets.
(defthm fn-bpnpf-valid-profile-opens
  (implies (and (fn-bpn-configp config) (fn-bpnpf-validp rows octets))
           (let ((st (fn-bpn-initial-machine-state config rows octets)))
             (and (fn-bpn-machine-statep st)
                  (equal (fn-bpn-machine-state-max-jobs st) rows)
                  (equal (fn-bpn-machine-state-max-octets st) octets)))))

; An admitted write never lowers a field in force.
(defthm fn-bpnpf-write-never-lowers
  (let ((w (fn-bpnpf-write-octets old rows octets)))
    (implies w
             (and (equal (fn-bpnpf-read t w) (list rows octets))
                  (<= (car old) rows) (<= (cadr old) octets))))
  :hints (("Goal" :in-theory (disable fn-bpnpf-read fn-bpnpf-octets))))
