; fn: ACL2-owned names for per-peer FNFD journals.
; A peer label is permitted to contain '/' and '.', so it is never a host path.
(in-package "ACL2")
(include-book "records")
(include-book "identity-invariants")

(defconst *fn-ff-max-name* 256)
(defconst *fn-ff-legacy-max-name* 250)
(defconst *fn-ff-chunk* 120)
(defconst *fn-ff-max-v1-chunks* 5)
(defconst *fn-ff-max-components* 7)
(defconst *fn-ff-v1* '(118 49))                 ; v1
(defconst *fn-ff-journal* '(106 111 117 114 110 97 108 46 102 110 102 100))
(defconst *fn-ff-suffix* '(46 102 110 102 100)) ; .fnfd

(defun fn-ff-namep (x)
  (declare (xargs :guard t))
  (and (fn-record-ascii-octet-listp x) (consp x) (<= (len x) *fn-ff-max-name*)))

(defun fn-ff-legacy-octetp (x)
  (declare (xargs :guard t))
  (or (and (natp x) (<= 48 x) (<= x 57))
      (and (natp x) (<= 65 x) (<= x 90))
      (and (natp x) (<= 97 x) (<= x 122))
      (equal x 45) (equal x 46) (equal x 95)))

(defun fn-ff-legacy-octet-listp (x)
  (declare (xargs :guard t))
  (if (consp x) (and (fn-ff-legacy-octetp (car x))
                     (fn-ff-legacy-octet-listp (cdr x)))
    (null x)))

(defun fn-feed-filename-legacy-safep (name)
  (declare (xargs :guard t))
  (and (fn-ff-namep name) (<= (len name) *fn-ff-legacy-max-name*)
       (fn-ff-legacy-octet-listp name)
       (not (equal name '(46))) (not (equal name '(46 46)))))

(defun fn-feed-filename-hex (xs)
  ; The identity codec owns lowercase hexadecimal and its inverse theorem.
  ; Keeping this named projection makes the FNFD layout's dependency explicit.
  (declare (xargs :guard (fn-cbor-octet-listp xs)))
  (fn-id-hex-octets xs))

(defun fn-ff-take (n xs)
  (declare (xargs :guard t))
  (if (and (posp n) (consp xs)) (cons (car xs) (fn-ff-take (1- n) (cdr xs))) nil))
(defun fn-ff-drop (n xs)
  (declare (xargs :guard t))
  (if (and (posp n) (consp xs)) (fn-ff-drop (1- n) (cdr xs)) xs))
(defun fn-ff-chunks-fuel (fuel xs)
  (declare (xargs :guard t))
  (if (and (posp fuel) (consp xs))
      (cons (fn-ff-take *fn-ff-chunk* xs)
            (fn-ff-chunks-fuel (1- fuel) (fn-ff-drop *fn-ff-chunk* xs))) nil))
(defun fn-ff-chunks (xs)
  (declare (xargs :guard t))
  (fn-ff-chunks-fuel (len xs) xs))

(defun fn-feed-filename-components (name)
  ; Successful output is a list of relative, nonempty ASCII components only.
  (declare (xargs :guard t))
  (if (not (fn-ff-namep name)) :bad
    (if (fn-feed-filename-legacy-safep name)
        (list (append name *fn-ff-suffix*))
      (append (list *fn-ff-v1*) (fn-ff-chunks (fn-feed-filename-hex name))
              (list *fn-ff-journal*)))))

(defun fn-feed-filename-layout (name)
  ; The migration decision: a safe old leaf remains its old leaf.  For every
  ; other name a host must use the v1 components and MUST NOT derive an old
  ; pathname from NAME; that old derivation is ambiguous or traversable.
  (declare (xargs :guard t))
  (if (not (fn-ff-namep name)) '(:refused :peer-name)
    (if (fn-feed-filename-legacy-safep name)
        (list :legacy (fn-feed-filename-components name))
      (list :v1 (fn-feed-filename-components name)))))

; Recovery accepts a filesystem component vector only by re-encoding its
; decoded peer and demanding byte-for-byte equality.  This keeps legacy leaf
; handling, v1 chunk boundaries and the inverse in one ACL2 owner.
(defun fn-ff-componentsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-record-ascii-octet-listp (car xs))
           (consp (car xs))
           (fn-ff-componentsp (cdr xs)))
    (null xs)))

(defun fn-ff-last (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (consp (cdr xs)) (fn-ff-last (cdr xs)) (car xs))
    nil))

(defun fn-ff-butlast (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (consp (cdr xs)))
      (cons (car xs) (fn-ff-butlast (cdr xs)))
    nil))

(defun fn-ff-append (left right)
  (declare (xargs :guard t))
  (if (consp left) (cons (car left) (fn-ff-append (cdr left) right)) right))

(defun fn-ff-append-components (xs)
  (declare (xargs :guard t))
  (if (consp xs) (fn-ff-append (car xs) (fn-ff-append-components (cdr xs))) nil))

(defun fn-ff-legacy-candidate (components)
  (declare (xargs :guard t))
  (if (not (true-listp components)) :bad
    (let ((leaf (car components)))
      (if (and (equal (len components) 1)
               (true-listp leaf)
               (<= (len *fn-ff-suffix*) (len leaf))
               (equal (fn-ff-drop (- (len leaf) (len *fn-ff-suffix*)) leaf)
                      *fn-ff-suffix*))
          (fn-ff-take (- (len leaf) (len *fn-ff-suffix*)) leaf)
        :bad))))

(defun fn-ff-v1-candidate (components)
  (declare (xargs :guard t))
  (if (and (true-listp components)
           (<= 3 (len components))
           (equal (car components) *fn-ff-v1*)
           (equal (fn-ff-last components) *fn-ff-journal*))
      (let ((hex (fn-ff-append-components (cdr (fn-ff-butlast components)))))
        (if (and (fn-id-hex-listp hex) (equal (mod (len hex) 2) 0))
            (fn-id-unhex hex)
          :bad))
    :bad))

(defun fn-feed-filename-from-components (components)
  ; `:bad' means refuse the on-disk entry.  It is never silently skipped:
  ; native recovery must report it as conflicting evidence.
  (declare (xargs :guard t))
  (if (not (fn-ff-componentsp components)) :bad
    (let ((name (if (equal (len components) 1)
                    (fn-ff-legacy-candidate components)
                  (fn-ff-v1-candidate components))))
      (if (and (fn-ff-namep name)
               (equal (fn-feed-filename-components name) components))
          name
        :bad))))

(defthm fn-feed-filename-hex-length
  (equal (len (fn-feed-filename-hex xs)) (* 2 (len xs)))
  :hints (("Goal" :in-theory (enable fn-feed-filename-hex)
           :use ((:instance fn-id-hex-octets-length (octets xs))))))

; This re-exports the identity codec's injectivity keystone for the exact
; projection this layout calls.  Its input domain is deliberately every octet
; list, wider than `fn-ff-namep'; the layout invokes it only after its bounded
; ASCII-name check.  Thus a host component equality is an equality of the peer
; octets ACL2 accepted, never a pathname normalization accident.
(defthm fn-feed-filename-hex-injective
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)
                (equal (fn-feed-filename-hex a) (fn-feed-filename-hex b)))
           (equal a b))
  :hints (("Goal" :in-theory (enable fn-feed-filename-hex)
           :use ((:instance fn-id-hex-octets-injective (a a) (b b)))))
  :rule-classes nil)
