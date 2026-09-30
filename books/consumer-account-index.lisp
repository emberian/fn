; Exact persistent character trie for the admitted native login domain.
; Root publication, carried alphabet/size facts, lifecycle and funding are
; separate obligations. No host path calls this source component yet.
(in-package "ACL2")
(include-book "msgid-index")
(include-book "cbor-invariants")

; Total representation conversion of one octet. Invalid external names must
; be refused by the bounded name gate, never authorized through its fallback.
(defun fn-cai-key-character (octet)
  (declare (xargs :guard t))
  (if (fn-cbor-octetp octet) (code-char octet) (code-char 0)))

; Proof abstraction only. Actual lookup/updates consume the already-parsed
; request octets one cell at a time and never allocate this character list.
(defun fn-cai-key (name)
  (declare (xargs :guard t))
  (if (consp name)
      (cons (fn-cai-key-character (car name)) (fn-cai-key (cdr name)))
    nil))

(defun fn-cai-get-octets (name trie)
  (declare (xargs :guard t))
  (if (consp name)
      (fn-cai-get-octets (cdr name)
                         (fn-midx-branch-get (fn-cai-key-character (car name)) trie))
    (fn-midx-branch-get *fn-midx-value-key* trie)))

(defun fn-cai-put-octets (name row trie)
  (declare (xargs :guard t))
  (if (consp name)
      (let ((key (fn-cai-key-character (car name))))
        (fn-midx-branch-put
         key (fn-cai-put-octets (cdr name) row (fn-midx-branch-get key trie)) trie))
    (fn-midx-branch-put *fn-midx-value-key* row trie)))

; The active caller supplies the actual auth grammar's established name
; bound (currently64), never the account count or cursor-ID ceiling.
(defun fn-cai-namep (name max-name)
  (declare (xargs :guard t))
  (and (natp max-name) (consp name) (fn-cbor-octet-listp name)
       (<= (len name) max-name)))

(defun fn-cai-lookup (name max-name trie)
  (declare (xargs :guard t))
  (and (fn-cai-namep name max-name) (fn-cai-get-octets name trie)))

(defthm fn-cai-key-is-characters
  (character-listp (fn-cai-key name))
  :hints (("Goal" :in-theory (enable fn-cai-key fn-cai-key-character
                                    fn-cbor-octetp))))

(defthm fn-cai-octet-character-is-injective
  (implies (and (fn-cbor-octetp x) (fn-cbor-octetp y))
           (equal (equal (fn-cai-key-character x) (fn-cai-key-character y))
                  (equal x y)))
  :hints (("Goal" :in-theory (e/d (fn-cai-key-character fn-cbor-octetp)
                                     (char-code-code-char-is-identity))
           :use ((:instance char-code-code-char-is-identity (n x))
                 (:instance char-code-code-char-is-identity (n y))))))

(defthm fn-cai-key-consp
  (equal (consp (fn-cai-key name)) (consp name))
  :hints (("Goal" :in-theory (enable fn-cai-key))))

(defthm fn-cai-octet-key-is-injective
  (implies (and (fn-cbor-octet-listp x) (fn-cbor-octet-listp y))
           (equal (equal (fn-cai-key x) (fn-cai-key y)) (equal x y)))
  :hints (("Goal" :induct (fn-midx-lookup-put-induct x y nil nil)
           :in-theory (e/d (fn-cai-key fn-cbor-octet-listp)
                            (fn-cai-key-character)))))

(defthm fn-cai-get-is-existing-trie-get
  (equal (fn-cai-get-octets name trie)
         (fn-midx-get-chars (fn-cai-key name) trie))
  :hints (("Goal" :induct (fn-cai-get-octets name trie)
           :in-theory (e/d (fn-cai-get-octets fn-cai-key fn-midx-get-chars)
                           (fn-midx-branch-get fn-cai-key-character)))))

(defthm fn-cai-put-is-existing-trie-put
  (equal (fn-cai-put-octets name row trie)
         (fn-midx-put-chars (fn-cai-key name) row trie))
  :hints (("Goal" :induct (fn-cai-put-octets name row trie)
           :in-theory (e/d (fn-cai-put-octets fn-cai-key fn-midx-put-chars)
                           (fn-midx-branch-get fn-midx-branch-put
                            fn-cai-key-character)))))

; Exact row association, with no hash/collision or reconstructed credentials.
; In particular an update for one login cannot change another account's
; incarnation/descriptor row, even when one name is a prefix of the other.
(defthm fn-cai-get-after-put-is-exact-row
  (implies (and (fn-cbor-octet-listp wanted) (fn-cbor-octet-listp name))
           (equal (fn-cai-get-octets wanted (fn-cai-put-octets name row trie))
                  (if (equal wanted name) row (fn-cai-get-octets wanted trie))))
  :hints (("Goal" :in-theory (disable fn-cai-get-octets fn-cai-put-octets
                                     fn-cai-key fn-midx-get-chars
                                     fn-midx-put-chars))))

(in-theory (disable fn-cai-key-character fn-cai-key fn-cai-get-octets
                    fn-cai-put-octets fn-cai-namep fn-cai-lookup))
