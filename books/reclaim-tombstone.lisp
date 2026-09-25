; fn: the tombstone a reclaimed article's payload becomes (D13, STO-014).
;
; Content reclamation (specs/storage.md, "History classes and lifetimes",
; capability C) removes an article's payload bytes and nothing else.  The
; article record stays where it was, with its Message-ID, groups, numbers,
; stamp, obligation identity, charge and content subject; only its payload
; octets are replaced by this fixed-shape block:
;
;   offset  0  8 octets  magic: NUL "FN-RCL1"
;           8  1 octet   1 when a source digest follows the octets digest
;           9 32 octets  SHA-256 of the removed payload
;          41 32 octets  SHA-256 of its D25 source (zeros when flag is 0)
;          73  8 octets  length of the removed payload, big-endian
;          81  8 octets  length A of the injecting agent, big-endian
;          89  A octets  the agent the payload's own Path line names
;
; The leading NUL is what no stored article begins with: an article opens
; with a header field name, and RFC 5322 field names are printable.  The
; recognizer below reads at most `*fn-rcl-tombstone-fixed*' conses of any
; payload, however large, so the served path that asks "is this reclaimed?"
; never walks an article.  No field is capped: the lengths are 64-bit (D27,
; bound work, never data).
;
; This book includes nothing: books/nntp-responses includes it for the
; served projection and books/store-reclaim for the decision.
(in-package "ACL2")

(defconst *fn-rcl-magic* '(0 70 78 45 82 67 76 49))   ; NUL "FN-RCL1"
(defconst *fn-rcl-tombstone-fixed* 89)

(defun fn-rcl-prefixp (prefix xs)
  (declare (xargs :guard (true-listp prefix)))
  (if (consp prefix)
      (and (consp xs)
           (equal (car prefix) (car xs))
           (fn-rcl-prefixp (cdr prefix) (cdr xs)))
    t))

; At least N conses; walks at most N.
(defun fn-rcl-at-leastp (n xs)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (consp xs) (fn-rcl-at-leastp (1- n) (cdr xs)))))

(defun fn-rcl-tombstonep (payload)
  (declare (xargs :guard t))
  (and (fn-rcl-at-leastp *fn-rcl-tombstone-fixed* payload)
       (fn-rcl-prefixp *fn-rcl-magic* payload)))

(defun fn-rcl-drop (n xs)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (not (consp xs))) xs (fn-rcl-drop (1- n) (cdr xs))))

(defun fn-rcl-take (n xs)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (not (consp xs))) nil
    (cons (car xs) (fn-rcl-take (1- n) (cdr xs)))))

(defun fn-rcl-u64-octets-aux (k n acc)
  (declare (xargs :guard (and (natp k) (natp n))))
  (if (zp k) acc
    (fn-rcl-u64-octets-aux (1- k) (floor n 256) (cons (mod n 256) acc))))

(defun fn-rcl-u64-octets (n)
  (declare (xargs :guard t))
  (fn-rcl-u64-octets-aux 8 (nfix n) nil))

(defun fn-rcl-octets-value (xs acc)
  (declare (xargs :guard (natp acc)))
  (if (consp xs)
      (fn-rcl-octets-value (cdr xs) (+ (* 256 acc) (nfix (car xs))))
    acc))

; The fields of a tombstone.
(defun fn-rcl-tomb-sourcep (tomb)
  (declare (xargs :guard t))
  (let ((x (fn-rcl-drop 8 tomb))) (and (consp x) (equal (car x) 1))))
(defun fn-rcl-tomb-octets-digest (tomb)
  (declare (xargs :guard t))
  (fn-rcl-take 32 (fn-rcl-drop 9 tomb)))
(defun fn-rcl-tomb-source-digest (tomb)
  (declare (xargs :guard t))
  (fn-rcl-take 32 (fn-rcl-drop 41 tomb)))
(defun fn-rcl-tomb-length (tomb)
  (declare (xargs :guard t))
  (fn-rcl-octets-value (fn-rcl-take 8 (fn-rcl-drop 73 tomb)) 0))
(defun fn-rcl-tomb-agent (tomb)
  (declare (xargs :guard t))
  (fn-rcl-drop 89 tomb))
