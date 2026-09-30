; Actual scalar/helper domains with literal positive and removal teeth.
(in-package "ACL2")
(include-book "../../books/payload-pull-runtime-workspace")

(defthm pawpo-actual-shift-complete-positive
 (let* ((bits (- (expt 2 31) 1)) (nbits 31) (octet 255))
  (and (fn-srp-pull-object-domain-p bits nbits octet)
       (natp (expt 2 nbits)) (<= (expt 2 nbits) (expt 2 31))
       (natp (* octet (expt 2 nbits)))
       (< (* octet (expt 2 nbits)) (expt 2 39))
       (natp (fn-zin-shift-in bits nbits octet))
       (< (fn-zin-shift-in bits nbits octet) (expt 2 39))
       (equal (fn-zin-shift-in bits nbits octet) (- (expt 2 39) 1))))
 :rule-classes nil)

(defthm pawpo-remove-shift-domain-corrupted-bits
 (and (not (fn-srp-pull-object-domain-p (expt 2 39) 0 0))
      (not (and (natp (expt 2 0)) (<= (expt 2 0) (expt 2 31))
                 (natp (* 0 (expt 2 0)))
                 (< (* 0 (expt 2 0)) (expt 2 39))
                 (natp (fn-zin-shift-in (expt 2 39) 0 0))
                 (< (fn-zin-shift-in (expt 2 39) 0 0) (expt 2 39)))))
 :rule-classes nil)

(defthm pawpo-actual-pull-helper-complete-positive
 (let* ((st (fn-zin-reset (create-fn-zin-st))) (fn-octets '(255)))
  (and (fn-pzw-state-bits-widthp st) (< (fn-zin-nbits st) 32)
       (< (fn-zin-nbits st) (fn-zin-need st))
       (fn-cbor-octetp (fn-octets-get 0 fn-octets))
       (fn-srp-pull-object-domain-p (fn-zin-bits st) (fn-zin-nbits st)
                                    (fn-octets-get 0 fn-octets))
       (fn-srp-pull-coordinate-p *fn-srp-selected-coordinate*
                                *fn-srp-selected-pull-body*)
       (equal (fn-assume-srp-pull-object-octets
                (fn-zin-bits st) (fn-zin-nbits st) (fn-octets-get 0 fn-octets)
                *fn-srp-selected-coordinate* *fn-srp-selected-pull-body*) 0)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-paw-actual-pull-helper-object-workspace-by-definition
   (coordinate *fn-srp-selected-coordinate*) (body *fn-srp-selected-pull-body*)
   (fn-zin-st (fn-zin-reset (create-fn-zin-st))) (ip 0) (fn-octets '(255)))))))

(defthm pawpo-remove-carried-bits-corrupted-state
 (let* ((st (fn-zin-set 1 1 (fn-zin-reset (create-fn-zin-st))))
        (fn-octets '(0)))
  (and (not (fn-pzw-state-bits-widthp st)) (< (fn-zin-nbits st) 32)
       (fn-cbor-octetp (fn-octets-get 0 fn-octets))
       (not (fn-srp-pull-object-domain-p (fn-zin-bits st) (fn-zin-nbits st)
                                        (fn-octets-get 0 fn-octets)))))
 :rule-classes nil)

(defthm pawpo-remove-prepull-width-corrupted-phase
 (let* ((st (fn-zin-set 2 32 (fn-zin-reset (create-fn-zin-st))))
        (fn-octets '(0)))
  (and (fn-pzw-state-bits-widthp st) (not (< (fn-zin-nbits st) 32))
       (fn-cbor-octetp (fn-octets-get 0 fn-octets))
       (not (fn-srp-pull-object-domain-p (fn-zin-bits st) (fn-zin-nbits st)
                                        (fn-octets-get 0 fn-octets)))))
 :rule-classes nil)

(defthm pawpo-remove-input-octet-corrupted-buffer
 (let* ((st (fn-zin-reset (create-fn-zin-st))) (fn-octets '(256)))
  (and (fn-pzw-state-bits-widthp st) (< (fn-zin-nbits st) 32)
       (not (fn-cbor-octetp (fn-octets-get 0 fn-octets)))
       (not (fn-srp-pull-object-domain-p (fn-zin-bits st) (fn-zin-nbits st)
                                        (fn-octets-get 0 fn-octets)))))
 :rule-classes nil)

(defthm pawpo-compiled-body-mutations-rejected
 (and (fn-srp-pull-coordinate-p *fn-srp-selected-coordinate*
                               *fn-srp-selected-pull-body*)
      (not (fn-srp-pull-coordinate-p *fn-srp-selected-coordinate*
                                    (cons "changed-source" (cdr *fn-srp-selected-pull-body*))))
      (not (fn-srp-pull-coordinate-p nil *fn-srp-selected-pull-body*)))
 :rule-classes nil)


(defthm pawpo-remove-needed-pull-bits-corrupted-state
 (let* ((st (fn-zin-set 1 1 (fn-zin-reset (create-fn-zin-st))))
        (fn-octets '(0)))
  (and (not (fn-pzw-state-bits-widthp st))
       (< (fn-zin-nbits st) (fn-zin-need st))
       (fn-cbor-octetp (fn-octets-get 0 fn-octets))
       (not (fn-srp-pull-object-domain-p (fn-zin-bits st) (fn-zin-nbits st)
                                        (fn-octets-get 0 fn-octets)))))
 :rule-classes nil)

(defthm pawpo-remove-needed-pull-condition-corrupted-phase
 (let* ((st (fn-zin-set 2 32 (fn-zin-reset (create-fn-zin-st))))
        (fn-octets '(0)))
  (and (fn-pzw-state-bits-widthp st)
       (not (< (fn-zin-nbits st) (fn-zin-need st)))
       (fn-cbor-octetp (fn-octets-get 0 fn-octets))
       (not (fn-srp-pull-object-domain-p (fn-zin-bits st) (fn-zin-nbits st)
                                        (fn-octets-get 0 fn-octets)))))
 :rule-classes nil)

(defthm pawpo-remove-needed-pull-octet-corrupted-buffer
 (let* ((st (fn-zin-reset (create-fn-zin-st))) (fn-octets '(256)))
  (and (fn-pzw-state-bits-widthp st)
       (< (fn-zin-nbits st) (fn-zin-need st))
       (not (fn-cbor-octetp (fn-octets-get 0 fn-octets)))
       (not (fn-srp-pull-object-domain-p (fn-zin-bits st) (fn-zin-nbits st)
                                        (fn-octets-get 0 fn-octets)))))
 :rule-classes nil)
