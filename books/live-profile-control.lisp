; Live heap preflight reads the profile decided by the owner, without a
; configuration-history observation. FNCT 26/27, bounded Mini read.
(in-package "ACL2")
(include-book "wire-grammar")
(include-book "byte-store-frame")
(include-book "defkeystone")

(defconst *fn-lpf-request-kind* 26)
(defconst *fn-lpf-reply-kind* 27)
(defconst *fn-lpf-request-grammar* '(:frame (70 78 67 84) 1 26 0 (:seq)))
(defconst *fn-lpf-reply-grammar*
  '(:frame (70 78 67 84) 1 27 634
    (:seq (:bytes 2 1 512 :utf8)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615)
          (:uint 8 0 18446744073709551615))))

(defun fn-lpf-request ()
  (declare (xargs :guard t))
  (fn-wg-encode *fn-lpf-request-grammar* nil))
(defun fn-lpf-request-p (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((r (fn-wg-decode *fn-lpf-request-grammar* octets)))
    (and (fn-wg-okp r) (null (fn-wg-rest r)))))
(defun fn-lpf-reply (profile)
  (declare (xargs :guard t))
  (and (fn-bs-profile-validp profile)
       (fn-wg-encode *fn-lpf-reply-grammar* profile)))
(defun fn-lpf-reply-read (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((r (fn-wg-decode *fn-lpf-reply-grammar* octets)))
    (and (fn-wg-okp r) (null (fn-wg-rest r))
         (fn-bs-profile-validp (fn-wg-value r)) (fn-wg-value r))))
(defun fn-lpf-reply-bound ()
  (declare (xargs :guard t))
  676)

(defun fn-lpf-request-size-p (n)
  (declare (xargs :guard t))
  (equal n *fn-frame-overhead-octets*))

(defthm fn-lpf-request-size-p-by-definition
  (equal (fn-lpf-request-size-p n) (equal n 42)))

(defthm fn-lpf-request-is-recognized
  (implies (equal octets (fn-lpf-request))
           (and (fn-lpf-request-p octets)
                (fn-lpf-request-size-p (len octets)))))

(defteeth fn-lpf-request-is-recognized
  :claim (((produced (equal octets (fn-lpf-request))))
          (and (fn-lpf-request-p octets) (fn-lpf-request-size-p (len octets))))
  :subject fn-lpf-request-p
  :witness ((octets (fn-lpf-request)))
  :breaks ((produced ((octets nil))))
  :mutations ((lost-request (:conclusion (not (fn-lpf-request-p octets)))
               ((octets (fn-lpf-request)))
               :fault "The owner does not recognize its client's request.")))

(defthm fn-lpf-grammars-are-grammars
  (and (fn-wg-grammarp *fn-lpf-request-grammar*)
       (fn-wg-grammarp *fn-lpf-reply-grammar*)))

(defthm fn-lpf-valid-profile-is-a-reply-value
  (implies (fn-bs-profile-validp profile)
           (fn-wg-valuep *fn-lpf-reply-grammar* profile))
  :hints (("Goal" :use ((:instance fn-bs-profile-validp-facts (values profile)))
           :in-theory (e/d (fn-wg-valuep-opener-frame fn-wg-valuep-opener-seq
                             fn-wg-valuep-opener-bytes fn-wg-valuep-opener-uint
                             fn-wg-encode-opener-seq fn-wg-encode-opener-bytes
                             fn-wg-encode-opener-uint fn-wg-class-okp fn-wg-utf8p
                             fn-frame-values-okp fn-frame-field-okp fn-frame-natp
                             fn-bs-meta-formatp fn-bs-meta-nth)
                            (fn-bs-profile-validp fn-bs-profile-invalid-reason
                             fn-frame-textp fn-wg-encode fn-wg-valuep)))))

(defthm fn-lpf-reply-round-trip
  (implies (fn-bs-profile-validp profile)
           (equal (fn-lpf-reply-read (fn-lpf-reply profile)) profile))
  :hints (("Goal" :use ((:instance fn-wg-decode-of-encode-whole
                                  (g *fn-lpf-reply-grammar*) (v profile)))
           :in-theory '(fn-lpf-reply-read fn-lpf-reply
                         fn-lpf-valid-profile-is-a-reply-value
                         fn-lpf-grammars-are-grammars
                         fn-wg-ok fn-wg-okp fn-wg-rest fn-wg-value
                         car-cons cdr-cons))))

(defteeth fn-lpf-reply-round-trip
  :claim (((valid (fn-bs-profile-validp profile)))
          (equal (fn-lpf-reply-read (fn-lpf-reply profile)) profile))
  :subject fn-lpf-reply-read
  :witness ((profile *fn-bs-profile-development*))
  :breaks ((valid ((profile '(invalid)))))
  :mutations ((lost-profile (:conclusion
                            (equal (fn-lpf-reply-read (fn-lpf-reply profile)) nil))
               ((profile *fn-bs-profile-development*))
               :fault "A client discards the owner's decided profile.")))

(defthm fn-lpf-reply-is-bounded
  (<= (len (fn-lpf-reply profile)) (fn-lpf-reply-bound))
  :hints (("Goal" :use (fn-lpf-valid-profile-is-a-reply-value)
           :in-theory (e/d (fn-lpf-reply fn-lpf-reply-bound
                             fn-wg-valuep-opener-frame fn-wg-encode-opener-frame
                             fn-wg-frame-protected)
                            (fn-bs-profile-validp fn-wg-valuep fn-wg-encode)))))

(defteeth fn-lpf-reply-is-bounded
  :claim (() (<= (len (fn-lpf-reply profile)) (fn-lpf-reply-bound)))
  :subject fn-lpf-reply
  :witness ((profile *fn-bs-profile-development*)) :breaks ()
  :mutations ((empty-budget (:conclusion (<= (len (fn-lpf-reply profile)) 0))
               ((profile *fn-bs-profile-development*))
               :fault "A zero reply budget cannot carry the decided profile.")))
