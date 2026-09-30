; Internal cold collector over the existing source/remap/census pipeline.
; No numeric count/pool caller arguments, source seal or allocation authority.
(in-package "ACL2")
(include-book "snapshot-source-cursor")
(include-book "snapshot-row-source-remap")
(include-book "history-census-controller")
(include-book "store-tree-size")
(include-book "recovery-source-authority")

; phase, literal typed cold descriptor, remapper, HCT, ORIGINALctx,
; same-producer fields, actual CP metadata or NIL, resource reference.
(defun fn-rcc-state (phase descriptor remapper census ctx fields cpmetadata resource)
 (declare (xargs :guard t))
 (list phase descriptor remapper census ctx fields cpmetadata resource))
(defun fn-rcc-begin (descriptor ctx fields cpmetadata resource)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((token (fn-omk-at 1 descriptor)) (count (fn-omk-at 6 descriptor))
        (frontier (fn-omk-at 7 descriptor)))
  (if (not (and (fn-omk-widthp descriptor 9)
                 (eq (fn-omk-at 0 descriptor) :recovery-census)
                 (fn-omk-widthp token 4) (eq (fn-omk-at 0 token) :recovery-source)
                 (natp (fn-omk-at 1 token))
                 (equal (fn-omk-at 2 token) (fn-omk-at 2 descriptor))
                 (natp (fn-omk-at 2 descriptor)) (natp (fn-omk-at 3 descriptor))
                 (natp (fn-omk-at 3 token)) (unsigned-byte-p 61 count)
                 (natp frontier) (fn-omk-widthp ctx 6)
                 (eq (fn-omk-at 0 ctx) :ok) (equal (fn-omk-at 1 ctx) count)
                 (fn-scs-fixed-carriesp 6 fields)))
      (mv :unavailable nil nil)
   (let* ((pair (list (fn-omk-at 1 token) count))
          ; Private census identity only. Actual RSA seal publishes source4.
          (private-source (list frontier pair 0 0))
          (source (fn-osrc-begin (fn-omk-at 5 descriptor) count frontier pair)))
    (mv :census source
     (fn-rcc-state :census descriptor (fn-osm-begin private-source)
      (fn-hct-begin count pair resource) ctx fields cpmetadata resource))))))

; Returned states must be the actual same pipeline. This fixed alignment gate
; is not proof of decoder/row provenance and does not make a supplied tuple an
; installed capability. The actual CURRENT cold wrapper owns that lineage.
(defun fn-rcc-offer (c source remapper census)
 (declare (xargs :guard t))
 (let* ((d (fn-omk-at 1 c)) (token (fn-omk-at 1 d))
        (count (fn-omk-at 6 d)) (frontier (fn-omk-at 7 d))
        (pair (fn-omk-at 5 census)) (rs (fn-omk-at 1 remapper)))
  (if (not (and (fn-omk-widthp c 8) (eq (fn-omk-at 0 c) :census)
                 (fn-omk-widthp d 9) (fn-omk-widthp token 4)
                 (fn-omk-widthp source 13) (fn-osrc-guardp source)
                 (fn-omk-widthp remapper 4) (fn-omk-tokenp rs)
                 (fn-hct-shapep census) (fn-omk-widthp pair 2)
                 (equal (fn-omk-at 0 pair) (fn-omk-at 1 token))
                 (equal (fn-omk-at 1 pair) count)
                 (equal (fn-omk-at 1 census) count)
                 (equal (fn-omk-at 3 source) count)
                 (equal (fn-omk-at 9 source) frontier)
                 (equal (fn-omk-at 10 source) pair)
                 (equal (fn-omk-at 0 rs) frontier)
                 (equal (fn-omk-at 0 (fn-omk-at 1 rs)) (fn-omk-at 0 pair))
                 (equal (fn-omk-at 1 (fn-omk-at 1 rs)) count)
                 (equal (fn-omk-at 2 rs) (fn-omk-at 12 source))))
      (mv :stale c)
   (mv :retained
    (fn-rcc-state :census d remapper census (fn-omk-at 4 c)
                   (fn-omk-at 5 c) (fn-omk-at 6 c) (fn-omk-at 7 c))))))
(defun fn-rcc-readout (c source remapper census)
 (declare (xargs :guard t))
 (mv-let (word next) (fn-rcc-offer c source remapper census)
  (declare (ignore next))
  (if (not (and (eq word :retained)
                 (eq (fn-omk-at 0 census) :prepared)
                 (eq (fn-omk-at 0 remapper) :idle)
                 (eq (fn-omk-at 0 source) :suffix)
                 (equal (fn-omk-at 2 source) (fn-omk-at 3 source))
                 (equal (fn-omk-at 2 census) (fn-omk-at 3 source))
                 (equal (fn-omk-at 3 (fn-omk-at 1 remapper))
                        (fn-omk-at 3 source))))
      (mv :pending nil c)
   ; This is an actual census result, not ready/sealed/funded metadata.
   (mv :measured
    (list :measured (fn-omk-at 1 (fn-omk-at 1 c))
          (fn-omk-at 2 census) (fn-omk-at 3 census)
          (fn-omk-at 4 c) (fn-omk-at 5 c) (fn-omk-at 6 c))
    (fn-rcc-state :measured (fn-omk-at 1 c) remapper census
      (fn-omk-at 4 c) (fn-omk-at 5 c) (fn-omk-at 6 c) (fn-omk-at 7 c))))))
(verify-guards fn-rcc-begin
 :hints (("Goal" :in-theory (enable unsigned-byte-p))))

; Fixed issuer-current check only. Frozen exclusive Store lifecycle carries
; same-count mutation exclusion; this never compares the retained Store graph.
(defun fn-rcc-currentp (c issuer epoch generation)
 (declare (xargs :guard t))
 (let* ((d (fn-omk-at 1 c)) (token (fn-omk-at 1 d)))
  (and (fn-omk-widthp c 8) (member-eq (fn-omk-at 0 c) '(:census :measured))
       (fn-omk-widthp d 9) (eq (fn-omk-at 0 d) :recovery-census)
       (equal (fn-omk-at 2 d) epoch) (equal (fn-omk-at 3 d) generation)
       (fn-rsa-currentp issuer token epoch generation)
       (equal (fn-omk-at 6 d) (fn-omk-at 4 issuer))
       (natp (fn-omk-at 7 d)) (natp (fn-omk-at 5 issuer))
       (<= (fn-omk-at 5 issuer) (fn-omk-at 7 d)))))
(defthm fn-rcc-measured-output-unfolds
 (implies (eq (mv-nth 0 (fn-rcc-readout c source remapper census)) :measured)
  (and (equal (mv-nth 1 (fn-rcc-readout c source remapper census))
              (list :measured (fn-omk-at 1 (fn-omk-at 1 c))
                    (fn-omk-at 6 (fn-omk-at 1 c)) (fn-omk-at 3 census)
                    (fn-omk-at 4 c) (fn-omk-at 5 c) (fn-omk-at 6 c)))
       (equal (mv-nth 2 (fn-rcc-readout c source remapper census))
              (fn-rcc-state :measured (fn-omk-at 1 c) remapper census
                    (fn-omk-at 4 c) (fn-omk-at 5 c) (fn-omk-at 6 c)
                    (fn-omk-at 7 c)))
       (equal (fn-omk-at 2 census) (fn-omk-at 1 census))
       (eq (fn-omk-at 0 census) :prepared)))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rcc-readout fn-rcc-offer fn-hct-shapep fn-hrcur-field fn-hrcur-widthp)
       (fn-rcc-state fn-omk-at fn-omk-widthp fn-osrc-guardp fn-omk-tokenp)))))
