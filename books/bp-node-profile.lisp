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
;
; Profile 2 (PRF-134, the codec half of P5) adds two fields: ADU octets, the
; largest application data unit the node admits (a whole bundle's payload or
; a fragment's total ADU length), and bundle octets, the largest bundle the
; node decodes from a peer.  Both are machine limits, raise only, with the
; pre-P5 constants as defaults (65,538 and 1 MiB); the held image's bound is
; OCTETS.  A format-1 file still opens, with those defaults
; (fn-bpnpf-profile-read-of-format-1).  The codec widths (*fn-bpa-max-octets*,
; *fn-bpb-max-input*, *fn-bpnf-max-held-image*) are the fields' ceiling,
; 2^24, so no profile is refused by a codec
; (books/bp-node-profile-admission, fn-bpnpf-profile-within-codec-widths).
;
; Work bounds stay constants and say so: *fn-bpn-machine-max-records* (4096
; lifecycle records between rotations), the TCPCL segment and transfer MRUs,
; and the profile file's read bound.
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

; -----------------------------------------------------------------------------
; Profile 2 (PRF-134): (ROWS OCTETS ADU BUNDLE).

(defconst *fn-bpnpf-format-2*
  '(102 110 45 98 112 45 112 114 111 102 105 108 101 45 50)) ; fn-bp-profile-2
(defconst *fn-bpnpf-spec-2* '(:text :nat :nat :nat :nat))
; The pre-P5 ADU record (65,538) and bundle decoder (1 MiB) bounds.
(defconst *fn-bpnpf-default-adu* 65538)
(defconst *fn-bpnpf-default-bundle* 1048576)

(defun fn-bpnpf-profile-validp (rows octets adu bundle)
  (declare (xargs :guard t))
  (and (fn-bpnpf-validp rows octets)
       (fn-bpn-machine-limitp adu) (fn-bpn-machine-limitp bundle)))

(defun fn-bpnpf-profilep (p)
  (declare (xargs :guard t))
  (and (true-listp p) (equal (len p) 4)
       (fn-bpnpf-profile-validp (car p) (cadr p) (caddr p) (cadddr p))))

(defun fn-bpnpf-adu-octets (p) (declare (xargs :guard t)) (fn-bpn-nth 2 p))
(defun fn-bpnpf-bundle-octets (p) (declare (xargs :guard t)) (fn-bpn-nth 3 p))

(defun fn-bpnpf-profile-default ()
  (declare (xargs :guard t))
  (list *fn-bpnpf-default-rows* *fn-bpnpf-default-octets*
        *fn-bpnpf-default-adu* *fn-bpnpf-default-bundle*))

(local
 (defthm fn-bpnpf-profile-values-ok
   (implies (fn-bpnpf-profile-validp rows octets adu bundle)
            (fn-frame-values-okp *fn-bpnpf-spec-2*
                                 (list *fn-bpnpf-format-2* rows octets adu bundle)))
   :hints (("Goal" :in-theory (enable fn-frame-values-okp fn-frame-field-okp)))))

(defun fn-bpnpf-profile-octets (rows octets adu bundle)
  (declare (xargs :guard t))
  (if (fn-bpnpf-profile-validp rows octets adu bundle)
      (fn-frame-fields-octets *fn-bpnpf-spec-2*
                              (list *fn-bpnpf-format-2* rows octets adu bundle))
    nil))

; The profile a journal opens under (the function the host calls,
; host/native/bp-service.lisp fnn-bps-read-profile).  A format-1 file, or
; none, is read by fn-bpnpf-read and takes the default ADU and bundle
; octets; a format-2 file is exactly one frame of a valid profile 2; anything
; else is NIL (the host refuses to open).
(defun fn-bpnpf-profile-read (present bytes)
  (declare (xargs :guard t))
  (let ((old (fn-bpnpf-read present bytes)))
    (if old
        (list (car old) (cadr old) *fn-bpnpf-default-adu*
              *fn-bpnpf-default-bundle*)
      (if (not (and present (fn-cbor-octet-listp bytes)))
          nil
        (let ((parsed (fn-frame-fields-parse *fn-bpnpf-spec-2* bytes)))
          (if (not (fn-frame-parse-okp parsed))
              nil
            (let ((v (fn-frame-parse-value parsed)))
              (if (and (true-listp v) (equal (len v) 5)
                       (equal (car v) *fn-bpnpf-format-2*)
                       (fn-bpnpf-profile-validp (nth 1 v) (nth 2 v)
                                                (nth 3 v) (nth 4 v)))
                  (list (nth 1 v) (nth 2 v) (nth 3 v) (nth 4 v))
                nil))))))))

(defun fn-bpnpf-profile-upgradep (old rows octets adu bundle)
  (declare (xargs :guard t))
  (and (fn-bpnpf-profilep old)
       (fn-bpnpf-profile-validp rows octets adu bundle)
       (<= (car old) rows) (<= (cadr old) octets)
       (<= (caddr old) adu) (<= (cadddr old) bundle)))

; The octets `bp-node profile' publishes: NIL (refused) unless the write
; raises or keeps every field of the profile in force.
(defun fn-bpnpf-profile-write-octets (old rows octets adu bundle)
  (declare (xargs :guard t))
  (if (fn-bpnpf-profile-upgradep old rows octets adu bundle)
      (fn-bpnpf-profile-octets rows octets adu bundle)
    nil))

(local
 (defthm fn-bpnpf-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; A format-2 frame is not a format-1 profile: the format-1 spec parses its
; first three fields and refuses the two that follow as trailing octets.
(local
 (defthm fn-bpnpf-format-2-octets-split
   (equal (fn-frame-fields-octets *fn-bpnpf-spec-2*
                                  (list f rows octets adu bundle))
          (append (fn-frame-fields-octets *fn-bpnpf-spec* (list f rows octets))
                  (fn-frame-fields-octets '(:nat :nat) (list adu bundle))))
   :hints (("Goal" :in-theory (e/d (fn-frame-fields-octets)
                                   (fn-frame-field-octets))
            :expand ((:free (x y) (append (fn-frame-field-octets :nat x)
                                          (fn-frame-field-octets :nat y))))))))

(local
 (defthm fn-bpnpf-two-nats-are-consp
   (consp (fn-frame-fields-octets '(:nat :nat) (list adu bundle)))
   :hints (("Goal" :in-theory (enable fn-frame-fields-octets
                                      fn-frame-field-octets)))))

(local
 (defthm fn-bpnpf-format-2-head-values-ok
   (implies (fn-bpnpf-validp rows octets)
            (fn-frame-values-okp *fn-bpnpf-spec*
                                 (list *fn-bpnpf-format-2* rows octets)))
   :hints (("Goal" :in-theory (enable fn-frame-values-okp fn-frame-field-okp)))))

(local
 (defthm fn-bpnpf-two-nats-values-ok
   (implies (and (fn-bpn-machine-limitp adu) (fn-bpn-machine-limitp bundle))
            (fn-frame-values-okp '(:nat :nat) (list adu bundle)))
   :hints (("Goal" :in-theory (enable fn-frame-values-okp fn-frame-field-okp)))))

(local
 (defthm fn-bpnpf-format-2-is-not-format-1
   (implies (fn-bpnpf-profile-validp rows octets adu bundle)
            (not (fn-bpnpf-read t (fn-bpnpf-profile-octets rows octets adu bundle))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnpf-profile-octets fn-frame-fields-parse)
                            (fn-frame-fields-octets fn-frame-fields-parse-aux
                             fn-bpnpf-validp fn-bpn-machine-limitp))
            :use ((:instance fn-frame-fields-parse-aux-of-octets
                   (specs *fn-bpnpf-spec*)
                   (values (list *fn-bpnpf-format-2* rows octets))
                   (rest (fn-frame-fields-octets '(:nat :nat) (list adu bundle))))
                  (:instance fn-frame-fields-octets-are-octets
                   (specs *fn-bpnpf-spec-2*)
                   (values (list *fn-bpnpf-format-2* rows octets adu bundle)))
                  (:instance fn-frame-fields-octets-are-octets
                   (specs '(:nat :nat))
                   (values (list adu bundle)))
                  (:instance fn-bpnpf-format-2-head-values-ok)
                  (:instance fn-bpnpf-two-nats-values-ok)
                  (:instance fn-bpnpf-profile-values-ok))))))

(defthm fn-bpnpf-profile-default-is-valid
  (fn-bpnpf-profilep (fn-bpnpf-profile-default)))

; Keystone: a saved profile 2 opens.  The octets written for every profile
; the relation admits read back as exactly that profile: no valid profile is
; one the file cannot carry.
(defthm fn-bpnpf-profile-read-of-octets
  (implies (fn-bpnpf-profile-validp rows octets adu bundle)
           (equal (fn-bpnpf-profile-read
                   t (fn-bpnpf-profile-octets rows octets adu bundle))
                  (list rows octets adu bundle)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpnpf-profile-octets)
                           (fn-frame-fields-octets fn-frame-fields-parse
                            fn-bpnpf-validp fn-bpnpf-read
                            fn-bpnpf-format-2-octets-split))
           :use ((:instance fn-bpnpf-format-2-is-not-format-1)
                 (:instance fn-frame-fields-parse-of-octets
                  (specs *fn-bpnpf-spec-2*)
                  (values (list *fn-bpnpf-format-2* rows octets adu bundle)))
                 (:instance fn-frame-fields-octets-are-octets
                  (specs *fn-bpnpf-spec-2*)
                  (values (list *fn-bpnpf-format-2* rows octets adu bundle)))))))

(local
 (defthm fn-bpnpf-read-absent
   (equal (fn-bpnpf-read nil bytes) (fn-bpnpf-default))))

; A profile saved before P5 (format 1), or none, opens with its rows and
; octets and the default ADU and bundle octets.
(defthm fn-bpnpf-profile-read-of-format-1
  (and (implies (fn-bpnpf-validp rows octets)
                (equal (fn-bpnpf-profile-read t (fn-bpnpf-octets rows octets))
                       (list rows octets *fn-bpnpf-default-adu*
                             *fn-bpnpf-default-bundle*)))
       (equal (fn-bpnpf-profile-read nil bytes) (fn-bpnpf-profile-default)))
  :hints (("Goal" :in-theory (disable fn-bpnpf-read fn-bpnpf-octets
                                      fn-bpnpf-validp)
           :use ((:instance fn-bpnpf-read-of-octets)
                 (:instance fn-bpnpf-read-absent)))))

; What the node reads is always a valid profile or a refusal.
(defthm fn-bpnpf-profile-read-is-valid
  (let ((p (fn-bpnpf-profile-read present bytes)))
    (implies p (fn-bpnpf-profilep p)))
  :hints (("Goal" :use ((:instance fn-bpnpf-read-is-valid))
           :in-theory (disable fn-bpnpf-read fn-bpnpf-read-is-valid
                               fn-frame-fields-parse))))

; Keystone: an admitted write never lowers a field in force, and it is read
; back as written.
(defthm fn-bpnpf-profile-write-never-lowers
  (let ((w (fn-bpnpf-profile-write-octets old rows octets adu bundle)))
    (implies w
             (and (equal (fn-bpnpf-profile-read t w)
                         (list rows octets adu bundle))
                  (<= (car old) rows) (<= (cadr old) octets)
                  (<= (caddr old) adu) (<= (cadddr old) bundle))))
  :hints (("Goal" :in-theory (disable fn-bpnpf-profile-read
                                      fn-bpnpf-profile-octets))))
