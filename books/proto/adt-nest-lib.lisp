; fn prototype (lane proto-adt-2, 2026-09-27): NESTED kinds, by flattening
; into the flat columns of books/proto/adt-lib.lisp.  NOT on a served path.
;
; A nested kind is a flat kind (adt-kindp) or
;   (:string)                 an ACL2 string, stored as its octets
;   (:prod K1 ... Kn)         a true list of n values (a nested record)
;   (:alt SYM K)              the symbol SYM, or a value of K (an option is
;                             (:alt nil K); fn-stxa's authored-source is
;                             (:alt :legacy (:octets)))
;   (:sum (TAG1 K1) ...)      a tag-headed value (TAG . PAYLOAD), PAYLOAD a
;                             value of the arm's kind; tags distinct symbols
; Its FLAT schema (adt-nflat) is a list of flat kinds: a string is one
; :octets column; a product its fields' columns; an alt a :bool presence
; column then K's columns; a sum an :enum tag column then every arm's
; columns (the arms not taken hold the arm's default).  adt-nfl flattens a
; value, adt-nunf reads it back (adt-nunf-nfl: the round trip), and the
; flat record is a record of the flat schema (adt-rec-p-nfl).  One flag
; argument FLG selects a kind (:k), a list of kinds (:ks) or a sum's arms
; (:arms), so every theorem here is one induction.

(in-package "ACL2")
(include-book "adt-key-lib")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable nth update-nth)))

; -----------------------------------------------------------------------------
; Strings as octets.

(defun adt-codes (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (atom cs) nil (cons (char-code (car cs)) (adt-codes (cdr cs)))))

(defun adt-chars (os)
  (declare (xargs :guard t))
  (if (atom os) nil (cons (code-char (if (unsigned-byte-p 8 (car os)) (car os) 0))
                          (adt-chars (cdr os)))))

(defun adt-str-octets (s)
  (declare (xargs :guard t))
  (adt-codes (coerce (if (stringp s) s "") 'list)))

(defun adt-octets-str (os)
  (declare (xargs :guard t))
  (coerce (adt-chars os) 'string))

(defthm adt-chars-codes
  (implies (character-listp cs) (equal (adt-chars (adt-codes cs)) cs)))

(defthm adt-octets-str-octets
  (implies (stringp s) (equal (adt-octets-str (adt-str-octets s)) s)))

(defthm adt-octetsp-codes
  (adt-octetsp (adt-codes cs)))

(defthm adt-octetsp-str-octets
  (adt-octetsp (adt-str-octets s)))

(defthm adt-str-octets-injective
  (implies (and (stringp a) (stringp b))
           (equal (equal (adt-str-octets a) (adt-str-octets b)) (equal a b)))
  :hints (("Goal" :use ((:instance adt-octets-str-octets (s a))
                        (:instance adt-octets-str-octets (s b)))
           :in-theory (disable adt-octets-str-octets adt-str-octets adt-octets-str))))

(in-theory (disable adt-str-octets adt-octets-str))

; -----------------------------------------------------------------------------
; Total list accessors (every function below has guard t).

(defmacro adt-hd (x) `(let ((adt-y ,x)) (if (consp adt-y) (car adt-y) nil)))
(defmacro adt-tl (x) `(let ((adt-y ,x)) (if (consp adt-y) (cdr adt-y) nil)))

; -----------------------------------------------------------------------------
; Kinds.

(defun adt-arm-tags (arms)
  (declare (xargs :guard t))
  (if (atom arms) nil (cons (if (consp (car arms)) (car (car arms)) nil) (adt-arm-tags (cdr arms)))))

(defun adt-nkind (flg x)
  (declare (xargs :guard t :measure (acl2-count x)))
  (case flg
    (:ks (if (atom x) (null x) (and (adt-nkind :k (car x)) (adt-nkind :ks (cdr x)))))
    (:arms (if (atom x) (null x)
             (and (consp (car x)) (symbolp (car (car x))) (car (car x)) (consp (cdr (car x)))
                  (null (adt-tl (adt-tl (car x))))
                  (adt-nkind :k (adt-hd (adt-tl (car x)))) (adt-nkind :arms (cdr x)))))
    (otherwise
     (and (consp x)
          (case (car x)
            (:string (null (cdr x)))
            (:prod (adt-nkind :ks (cdr x)))
            (:alt (and (consp (cdr x)) (symbolp (adt-hd (adt-tl x))) (consp (adt-tl (adt-tl x))) (null (adt-tl (adt-tl (adt-tl x))))
                       (adt-nkind :k (adt-hd (adt-tl (adt-tl x))))))
            (:sum (and (consp (cdr x)) (adt-nkind :arms (cdr x))
                       (no-duplicatesp-equal (adt-arm-tags (cdr x)))))
            (otherwise (adt-kindp x)))))))

(defun adt-leaf-kind-p (x)
  (declare (xargs :guard t))
  (and (consp x) (not (member-eq (car x) '(:string :prod :alt :sum)))))

; -----------------------------------------------------------------------------
; The flat schema, defaults, flattening, reading back, validity.

(defun adt-nflat (flg x)
  (declare (xargs :guard t :measure (acl2-count x)))
  (case flg
    (:ks (if (atom x) nil (append (adt-nflat :k (car x)) (adt-nflat :ks (cdr x)))))
    (:arms (if (atom x) nil
             (append (adt-nflat :k (if (consp (car x)) (adt-hd (adt-tl (car x))) nil)) (adt-nflat :arms (cdr x)))))
    (otherwise
     (if (atom x) nil
       (case (car x)
         (:string (list '(:octets)))
         (:prod (adt-nflat :ks (cdr x)))
         (:alt (cons '(:bool) (adt-nflat :k (adt-hd (adt-tl (adt-tl x))))))
         (:sum (cons (cons :enum (adt-arm-tags (cdr x))) (adt-nflat :arms (cdr x))))
         (otherwise (list x)))))))

(defun adt-ndef (flg x)
  ; the default value (FLG :k) or record (:ks)
  (declare (xargs :guard t :measure (acl2-count x)))
  (case flg
    (:ks (if (atom x) nil (cons (adt-ndef :k (car x)) (adt-ndef :ks (cdr x)))))
    (otherwise
     (if (atom x) nil
       (case (car x)
         (:string "")
         (:prod (adt-ndef :ks (cdr x)))
         (:alt (adt-hd (adt-tl x)))
         (:sum (let ((arm (if (consp (cdr x)) (adt-hd (adt-tl x)) nil)))
                 (cons (if (consp arm) (car arm) nil)
                       (adt-ndef :k (if (consp arm) (if (consp (cdr arm)) (adt-hd (adt-tl arm)) nil) nil)))))
         ((:u8 :u32 :u64 :nat) 0)
         (:enum (if (consp (cdr x)) (adt-hd (adt-tl x)) nil))
         (otherwise nil))))))

(defun adt-nfl (flg x v)
  ; the flat cells of V; for :arms, V is the whole sum value
  (declare (xargs :guard t :measure (acl2-count x)))
  (case flg
    (:ks (if (atom x) nil
           (append (adt-nfl :k (car x) (if (consp v) (car v) nil))
                   (adt-nfl :ks (cdr x) (if (consp v) (cdr v) nil)))))
    (:arms (if (atom x) nil
             (let ((k (if (consp (car x)) (adt-hd (adt-tl (car x))) nil)))
               (append (adt-nfl :k k (if (and (consp (car x)) (consp v) (equal (car v) (car (car x))))
                                         (cdr v)
                                       (adt-ndef :k k)))
                       (adt-nfl :arms (cdr x) v)))))
    (otherwise
     (if (atom x) nil
       (case (car x)
         (:string (list (adt-str-octets v)))
         (:prod (adt-nfl :ks (cdr x) v))
         (:alt (if (equal v (adt-hd (adt-tl x)))
                   (cons nil (adt-nfl :k (adt-hd (adt-tl (adt-tl x))) (adt-ndef :k (adt-hd (adt-tl (adt-tl x))))))
                 (cons t (adt-nfl :k (adt-hd (adt-tl (adt-tl x))) v))))
         (:sum (cons (if (consp v) (car v) nil) (adt-nfl :arms (cdr x) v)))
         (otherwise (list v)))))))

(defun adt-nunf (flg x w tag)
  ; (value . rest): reads what adt-nfl wrote; TAG selects the arm (:arms)
  (declare (xargs :guard t :measure (acl2-count x)))
  (case flg
    (:ks (if (atom x) (cons nil w)
           (let* ((r1 (adt-nunf :k (car x) w nil))
                  (r2 (adt-nunf :ks (cdr x) (cdr r1) nil)))
             (cons (cons (car r1) (car r2)) (cdr r2)))))
    (:arms (if (atom x) (cons nil w)
             (let* ((r1 (adt-nunf :k (if (consp (car x)) (adt-hd (adt-tl (car x))) nil) w nil))
                    (r2 (adt-nunf :arms (cdr x) (cdr r1) tag)))
               (cons (if (and (consp (car x)) (equal tag (car (car x)))) (car r1) (car r2))
                     (cdr r2)))))
    (otherwise
     (if (atom x) (cons nil w)
       (case (car x)
         (:string (cons (adt-octets-str (if (consp w) (car w) nil)) (if (consp w) (cdr w) nil)))
         (:prod (adt-nunf :ks (cdr x) w nil))
         (:alt (let ((r (adt-nunf :k (adt-hd (adt-tl (adt-tl x))) (if (consp w) (cdr w) nil) nil)))
                 (cons (if (and (consp w) (car w)) (car r) (adt-hd (adt-tl x))) (cdr r))))
         (:sum (let ((r (adt-nunf :arms (cdr x) (if (consp w) (cdr w) nil) (if (consp w) (car w) nil))))
                 (cons (cons (if (consp w) (car w) nil) (car r)) (cdr r))))
         (otherwise (cons (if (consp w) (car w) nil) (if (consp w) (cdr w) nil))))))))

(defun adt-nval (flg x v)
  (declare (xargs :guard t :measure (acl2-count x)))
  (case flg
    (:ks (if (atom x) (null v)
           (and (consp v) (adt-nval :k (car x) (car v)) (adt-nval :ks (cdr x) (cdr v)))))
    (:arms (if (atom x) t
             (and (if (and (consp (car x)) (consp v) (equal (car v) (car (car x))))
                      (adt-nval :k (adt-hd (adt-tl (car x))) (cdr v))
                    t)
                  (adt-nval :arms (cdr x) v))))
    (otherwise
     (if (atom x) nil
       (case (car x)
         (:string (stringp v))
         (:prod (adt-nval :ks (cdr x) v))
         (:alt (or (equal v (adt-hd (adt-tl x)))
                   (and (adt-nval :k (adt-hd (adt-tl (adt-tl x))) v) (not (equal v (adt-hd (adt-tl x)))))))
         (:sum (and (consp v) (member-equal (car v) (adt-arm-tags (cdr x)))
                    (adt-nval :arms (cdr x) v)))
         (otherwise (and (adt-kindp x) (adt-val-okp x v))))))))

; -----------------------------------------------------------------------------
; The round trip, one induction over the flag.

(defun adt-n-induct (flg x v rest)
  (declare (xargs :measure (acl2-count x) :verify-guards nil))
  (case flg
    (:ks (if (atom x) (list v rest)
           (list (adt-n-induct :k (car x) (if (consp v) (car v) nil)
                               (append (adt-nfl :ks (cdr x) (if (consp v) (cdr v) nil)) rest))
                 (adt-n-induct :ks (cdr x) (if (consp v) (cdr v) nil) rest))))
    (:arms (if (atom x) (list v rest)
             (let ((k (if (consp (car x)) (adt-hd (adt-tl (car x))) nil)))
               (list (adt-n-induct :k k (if (and (consp (car x)) (consp v) (equal (car v) (car (car x))))
                                            (cdr v)
                                          (adt-ndef :k k))
                                   (append (adt-nfl :arms (cdr x) v) rest))
                     (adt-n-induct :arms (cdr x) v rest)))))
    (otherwise
     (if (atom x) (list v rest)
       (case (car x)
         (:prod (adt-n-induct :ks (cdr x) v rest))
         (:alt (list (adt-n-induct :k (adt-hd (adt-tl (adt-tl x))) (adt-ndef :k (adt-hd (adt-tl (adt-tl x)))) rest)
                     (adt-n-induct :k (adt-hd (adt-tl (adt-tl x))) v rest)))
         (:sum (adt-n-induct :arms (cdr x) v rest))
         (otherwise (list v rest)))))))

(defun adt-ndef-induct (flg x)
  (declare (xargs :measure (acl2-count x)))
  (case flg
    (:ks (if (atom x) nil (list (adt-ndef-induct :k (car x)) (adt-ndef-induct :ks (cdr x)))))
    (:arms (if (atom x) nil (list (adt-ndef-induct :k (if (consp (car x)) (adt-hd (adt-tl (car x))) nil))
                                  (adt-ndef-induct :arms (cdr x)))))
    (otherwise
     (if (atom x) nil
       (case (car x)
         (:prod (adt-ndef-induct :ks (cdr x)))
         (:alt (adt-ndef-induct :k (adt-hd (adt-tl (adt-tl x)))))
         (:sum (adt-ndef-induct :arms (cdr x)))
         (otherwise nil))))))

(defthm adt-nval-arms-absent
  (implies (not (member-equal (car v) (adt-arm-tags x)))
           (adt-nval :arms x v))
  :hints (("Goal" :induct (adt-arm-tags x) :expand ((adt-nval :arms x v)))))

(defun adt-arms-defs-ok (x)
  (declare (xargs :verify-guards nil))
  (if (atom x) t
    (and (adt-nval :k (adt-hd (adt-tl (car x))) (adt-ndef :k (adt-hd (adt-tl (car x)))))
         (adt-arms-defs-ok (cdr x)))))

(defthm adt-nval-ndef-flag
  (implies (adt-nkind flg x)
           (if (equal flg :arms)
               (adt-arms-defs-ok x)
             (adt-nval flg x (adt-ndef flg x))))
  :rule-classes nil
  :hints (("Goal" :induct (adt-ndef-induct flg x) :in-theory (enable adt-val-okp)
           :expand ((adt-ndef flg x) (adt-nval flg x (adt-ndef flg x))
                    (adt-nval :arms (cdr x) (adt-ndef flg x))
                    (adt-nkind :arms (cdr x))))))

(defthm adt-nval-ndef
  (implies (and (adt-nkind flg x) (not (equal flg :arms)))
           (adt-nval flg x (adt-ndef flg x)))
  :hints (("Goal" :use adt-nval-ndef-flag)))

(defun adt-arm-of (tag arms)
  ; the payload position: is TAG an arm's tag
  (declare (xargs :guard t))
  (if (member-equal tag (adt-arm-tags arms)) t nil))

(local
 (defthm adt-append-assoc-n
   (equal (append (append a b) c) (append a (append b c)))))

(defthm adt-nunf-nfl
  (implies (and (adt-nkind flg x) (adt-nval flg x v))
           (equal (adt-nunf flg x (append (adt-nfl flg x v) rest)
                            (if (and (equal flg :arms) (consp v)) (car v) nil))
                  (case flg
                    (:arms (cons (if (and (consp v) (member-equal (car v) (adt-arm-tags x))) (cdr v) nil)
                                 rest))
                    (otherwise (cons v rest)))))
  :hints (("Goal" :induct (adt-n-induct flg x v rest)
           :expand ((:free (w tag) (adt-nunf flg x w tag))
                    (adt-nfl flg x v)))))

; -----------------------------------------------------------------------------
; The flat record is a record of the flat schema.

(defthm adt-rec-p-append
  (implies (and (adt-rec-p s1 r1) (adt-rec-p s2 r2))
           (adt-rec-p (append s1 s2) (append r1 r2)))
  :hints (("Goal" :in-theory (enable adt-rec-p))))

(defthm adt-schemap-append
  (implies (and (adt-schemap s1) (adt-schemap s2)) (adt-schemap (append s1 s2))))

(defthm adt-rec-p-nfl-flag
  (implies (and (adt-nkind flg x) (adt-nval flg x v))
           (and (adt-schemap (adt-nflat flg x))
                (adt-rec-p (adt-nflat flg x) (adt-nfl flg x v))))
  :rule-classes nil
  :hints (("Goal" :induct (adt-n-induct flg x v rest)
           :in-theory (enable adt-rec-p adt-val-okp)
           :expand ((adt-nfl flg x v) (adt-nflat flg x)))))

(defthm adt-rec-p-nfl
  (implies (and (adt-nkind flg x) (adt-nval flg x v))
           (adt-rec-p (adt-nflat flg x) (adt-nfl flg x v)))
  :hints (("Goal" :use adt-rec-p-nfl-flag)))

(defthm adt-schemap-nflat
  (implies (and (adt-nkind flg x) (adt-nval flg x v))
           (adt-schemap (adt-nflat flg x)))
  :hints (("Goal" :use adt-rec-p-nfl-flag)))

(defthm adt-len-nfl
  (equal (len (adt-nfl flg x v)) (len (adt-nflat flg x)))
  :hints (("Goal" :induct (adt-n-induct flg x v rest)
           :expand ((adt-nfl flg x v) (adt-nflat flg x)))))

(defthm adt-true-listp-nfl
  (true-listp (adt-nfl flg x v))
  :hints (("Goal" :induct (adt-n-induct flg x v rest) :expand ((adt-nfl flg x v)))))

; -----------------------------------------------------------------------------
; Records of a nested schema S (a list of nested kinds), as flat records.

(defun adt-nrec (s r)
  (declare (xargs :verify-guards nil))
  (adt-nfl :ks s r))

(defun adt-nunrec (s w)
  (declare (xargs :verify-guards nil))
  (car (adt-nunf :ks s w nil)))

(defun adt-nmap (s a)
  (declare (xargs :verify-guards nil))
  (if (atom a) nil (cons (adt-nrec s (car a)) (adt-nmap s (cdr a)))))

(defun adt-nseq-p (s a)
  (declare (xargs :verify-guards nil))
  (if (atom a) (null a) (and (adt-nval :ks s (car a)) (adt-nseq-p s (cdr a)))))

(defthm adt-nunrec-nrec
  (implies (and (adt-nkind :ks s) (adt-nval :ks s r))
           (equal (adt-nunrec s (adt-nrec s r)) r))
  :hints (("Goal" :use ((:instance adt-nunf-nfl (flg :ks) (x s) (v r) (rest nil))))))

(defthm adt-seq-p-nmap
  (implies (and (adt-nkind :ks s) (adt-nseq-p s a))
           (adt-seq-p (adt-nflat :ks s) (adt-nmap s a))))

; The key: field J of S is a flat or string kind; its flat cell is at
; (adt-flat-index s j), holding (adt-fkey kind value).
(defun adt-key-kind-p (k)
  (declare (xargs :guard t))
  (or (equal k '(:string)) (and (adt-kindp k) (adt-leaf-kind-p k))))

(defun adt-fkey (k v)
  (declare (xargs :guard t))
  (if (equal k '(:string)) (adt-str-octets v) v))

(defun adt-flat-index (s j)
  (declare (xargs :verify-guards nil))
  (len (adt-nflat :ks (take j s))))

(local
 (defun adt-sj-induct (s j r)
   (if (or (zp j) (atom s)) (list s j r) (adt-sj-induct (cdr s) (1- j) (cdr r)))))

(local
 (defthm adt-nth-append-local
   (implies (natp n)
            (equal (nth n (append x y)) (if (< n (len x)) (nth n x) (nth (- n (len x)) y))))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm adt-nth-flat-index
  (implies (and (adt-nkind :ks s) (adt-nval :ks s r) (natp j) (< j (len s))
                (adt-key-kind-p (nth j s)))
           (equal (nth (adt-flat-index s j) (adt-nrec s r))
                  (adt-fkey (nth j s) (nth j r))))
  :hints (("Goal" :induct (adt-sj-induct s j r)
           :in-theory (enable nth)
           :expand ((adt-nfl :ks s r) (adt-nflat :ks (take j s)) (adt-nfl :k (car s) (car r))
                    (adt-nflat :k (car s))))))

(defthm adt-fkey-injective
  (implies (and (adt-key-kind-p k) (adt-nval :k k v1) (adt-nval :k k v2))
           (equal (equal (adt-fkey k v1) (adt-fkey k v2)) (equal v1 v2))))

(defthm adt-nval-nth
  (implies (and (adt-nval :ks s r) (natp j) (< j (len s)))
           (adt-nval :k (nth j s) (nth j r)))
  :hints (("Goal" :induct (adt-sj-induct s j r) :in-theory (enable nth))))

(defthm adt-key-cell-equal
  (implies (and (adt-nkind :ks s) (adt-nval :ks s r) (natp j) (< j (len s))
                (adt-key-kind-p (nth j s)) (adt-nval :k (nth j s) k))
           (equal (equal (nth (adt-flat-index s j) (adt-nrec s r)) (adt-fkey (nth j s) k))
                  (equal (nth j r) k)))
  :hints (("Goal" :in-theory (disable adt-fkey adt-nrec adt-flat-index adt-key-kind-p))))

(defthm adt-rec-p-nrec
  (implies (and (adt-nkind :ks s) (adt-nval :ks s r))
           (adt-rec-p (adt-nflat :ks s) (adt-nrec s r))))

(in-theory (disable adt-nrec adt-flat-index adt-fkey adt-key-kind-p))

(defthm adt-kmem-nmap
  (implies (and (adt-nkind :ks s) (adt-nseq-p s a) (natp j) (< j (len s))
                (adt-key-kind-p (nth j s)) (adt-nval :k (nth j s) k))
           (equal (adt-kmem (adt-flat-index s j) (adt-fkey (nth j s) k) (adt-nmap s a))
                  (adt-kmem j k a)))
  :hints (("Goal" :in-theory (enable adt-kmem))))

(defthm adt-kfind-nmap
  (implies (and (adt-nkind :ks s) (adt-nseq-p s a) (natp j) (< j (len s))
                (adt-key-kind-p (nth j s)) (adt-nval :k (nth j s) k))
           (equal (adt-kfind (adt-flat-index s j) (adt-fkey (nth j s) k) (adt-nmap s a))
                  (if (adt-kmem j k a) (adt-nrec s (adt-kfind j k a)) nil)))
  :hints (("Goal" :in-theory (enable adt-kmem))))

(defthm adt-kremove-nmap
  (implies (and (adt-nkind :ks s) (adt-nseq-p s a) (natp j) (< j (len s))
                (adt-key-kind-p (nth j s)) (adt-nval :k (nth j s) k))
           (equal (adt-kremove (adt-flat-index s j) (adt-fkey (nth j s) k) (adt-nmap s a))
                  (adt-nmap s (adt-kremove j k a)))))

(local
 (defthm adt-kunique-consp
   (implies (consp a)
            (equal (adt-kunique j a)
                   (and (not (adt-kmem j (nth j (car a)) (cdr a))) (adt-kunique j (cdr a)))))
   :hints (("Goal" :in-theory (enable adt-kunique adt-kmem)))))

(defthm adt-kunique-nmap
  (implies (and (adt-nkind :ks s) (adt-nseq-p s a) (natp j) (< j (len s))
                (adt-key-kind-p (nth j s)))
           (equal (adt-kunique (adt-flat-index s j) (adt-nmap s a))
                  (adt-kunique j a)))
  :hints (("Goal" :induct (adt-nmap s a)
           :in-theory (e/d (adt-kunique-cons) (adt-kmem-nmap)))
          ("Subgoal *1/2" :use ((:instance adt-kmem-nmap (a (cdr a)) (k (nth j (car a))))
                                (:instance adt-nth-flat-index (r (car a)))))))

(defthm adt-kinsert-nmap
  (equal (adt-kinsert dir (adt-nrec s r) (adt-nmap s a))
         (adt-nmap s (adt-kinsert dir r a)))
  :hints (("Goal" :in-theory (enable adt-kinsert))))

(defthm adt-nmap-append
  (equal (adt-nmap s (append x y)) (append (adt-nmap s x) (adt-nmap s y))))

(defthm adt-kreplace-found-nmap
  (implies (and (adt-nkind :ks s) (adt-nseq-p s a) (adt-nval :ks s r) (natp j) (< j (len s))
                (adt-key-kind-p (nth j s)))
           (equal (adt-kreplace-found (adt-flat-index s j) (adt-nrec s r) (adt-nmap s a))
                  (adt-nmap s (adt-kreplace-found j r a))))
  :hints (("Goal" :in-theory (disable adt-key-cell-equal)
           :induct (adt-nmap s a))
          ("Subgoal *1/1" :use ((:instance adt-key-cell-equal (r (car a)) (k (nth j r)))
                                (:instance adt-nth-flat-index)))))

(defthm adt-kreplace-nmap
  (implies (and (adt-nkind :ks s) (adt-nseq-p s a) (adt-nval :ks s r) (natp j) (< j (len s))
                (adt-key-kind-p (nth j s)))
           (equal (adt-kreplace dir (adt-flat-index s j) (adt-nrec s r) (adt-nmap s a))
                  (adt-nmap s (adt-kreplace dir j r a))))
  :hints (("Goal" :in-theory (e/d (adt-kreplace) (adt-kmem-nmap adt-kinsert))
           :use ((:instance adt-kmem-nmap (k (nth j r)))
                 (:instance adt-nth-flat-index)))))

(defthm adt-nseq-p-true-listp
  (implies (adt-nseq-p s a) (true-listp a))
  :rule-classes :forward-chaining)

; -----------------------------------------------------------------------------
; A keyed set of NESTED records: the flat keyed set of their flat records.
; S is the nested schema, J the key field (a flat or string kind).

(defthm adt-nseq-p-kinsert
  (implies (and (adt-nseq-p s a) (adt-nval :ks s r)) (adt-nseq-p s (adt-kinsert dir r a)))
  :hints (("Goal" :in-theory (enable adt-kinsert))))

(defthm adt-nseq-p-kremove
  (implies (adt-nseq-p s a) (adt-nseq-p s (adt-kremove j k a))))

(defthm adt-nseq-p-kreplace
  (implies (and (adt-nseq-p s a) (adt-nval :ks s r)) (adt-nseq-p s (adt-kreplace dir j r a)))
  :hints (("Goal" :in-theory (enable adt-kreplace))))

(defthm adt-nseq-p-kfind
  (implies (and (adt-nseq-p s a) (adt-kmem j k a)) (adt-nval :ks s (adt-kfind j k a)))
  :hints (("Goal" :in-theory (enable adt-kmem))))

(defun adt-nkcorr (s dir j c a)
  (declare (xargs :verify-guards nil))
  (and (adt-nkind :ks s) (adt-nseq-p s a) (natp j) (< j (len s))
       (adt-key-kind-p (nth j s))
       (adt-kcorr (adt-nflat :ks s) dir (adt-flat-index s j) c (adt-nmap s a))))

(defun adt-nkempty-c (s)
  (declare (xargs :verify-guards nil))
  (adt-kempty-c (adt-nflat :ks s)))

(defun adt-nkmem-c (s j k c)
  (declare (xargs :verify-guards nil))
  (adt-kmem-c (adt-nflat :ks s) (adt-flat-index s j) (adt-fkey (nth j s) k) c))

(defun adt-nkfind-c (s j k c)
  (declare (xargs :verify-guards nil))
  (if (adt-nkmem-c s j k c)
      (adt-nunrec s (adt-kfind-c (adt-nflat :ks s) (adt-flat-index s j) (adt-fkey (nth j s) k) c))
    nil))

(defun adt-nkinsert-c (s j r c)
  (declare (xargs :verify-guards nil))
  (adt-kinsert-c (adt-nflat :ks s) (adt-flat-index s j) (adt-nrec s r) c))

(defun adt-nkremove-c (s j k c)
  (declare (xargs :verify-guards nil))
  (adt-kremove-c (adt-nflat :ks s) (adt-flat-index s j) (adt-fkey (nth j s) k) c))

(defun adt-nkreplace-c (s j r c)
  (declare (xargs :verify-guards nil))
  (adt-kreplace-c (adt-nflat :ks s) (adt-flat-index s j) (adt-nrec s r) c))

(local
 (defthm adt-flat-key-of-nrec
   (implies (and (adt-nkind :ks s) (adt-nval :ks s r) (natp j) (< j (len s))
                 (adt-key-kind-p (nth j s)))
            (equal (nth (adt-flat-index s j) (adt-nrec s r)) (adt-fkey (nth j s) (nth j r))))))

(defthm adt-nkcorr-empty
  (implies (and (adt-nkind :ks s) (natp j) (< j (len s)) (adt-key-kind-p (nth j s))
                (adt-schemap (adt-nflat :ks s))
                (< (adt-flat-index s j) (len (adt-nflat :ks s))))
           (adt-nkcorr s dir j (adt-nkempty-c s) nil)))

(defthm adt-nkcorr-mem
  (implies (and (adt-nkcorr s dir j c a) (adt-nval :k (nth j s) k))
           (equal (adt-nkmem-c s j k c) (adt-kmem j k a))))

(defthm adt-nkcorr-find
  (implies (and (adt-nkcorr s dir j c a) (adt-nval :k (nth j s) k))
           (equal (adt-nkfind-c s j k c) (adt-kfind j k a))))

(defthm adt-nkcorr-insert
  (implies (and (adt-nkcorr s dir j c a) (adt-nval :ks s r) (not (adt-kmem j (nth j r) a)))
           (adt-nkcorr s dir j (adt-nkinsert-c s j r c) (adt-kinsert dir r a)))
  :hints (("Goal" :in-theory (e/d (adt-nkcorr adt-nkinsert-c) (adt-kcorr-insert adt-kinsert-nmap))
           :use ((:instance adt-kcorr-insert (s (adt-nflat :ks s)) (j (adt-flat-index s j))
                            (r (adt-nrec s r)) (a (adt-nmap s a)))
                 (:instance adt-kinsert-nmap)
                 (:instance adt-kmem-nmap (k (nth j r)))))))

(defthm adt-nkcorr-remove
  (implies (and (adt-nkcorr s dir j c a) (adt-nval :k (nth j s) k))
           (adt-nkcorr s dir j (adt-nkremove-c s j k c) (adt-kremove j k a)))
  :hints (("Goal" :in-theory (e/d (adt-nkcorr adt-nkremove-c) (adt-kcorr-remove))
           :use ((:instance adt-kcorr-remove (s (adt-nflat :ks s)) (j (adt-flat-index s j))
                            (k (adt-fkey (nth j s) k)) (a (adt-nmap s a)))))))

(defthm adt-nkcorr-replace
  (implies (and (adt-nkcorr s dir j c a) (adt-nval :ks s r))
           (adt-nkcorr s dir j (adt-nkreplace-c s j r c) (adt-kreplace dir j r a)))
  :hints (("Goal" :in-theory (e/d (adt-nkcorr adt-nkreplace-c) (adt-kcorr-replace adt-kreplace-nmap))
           :use ((:instance adt-kcorr-replace (s (adt-nflat :ks s)) (j (adt-flat-index s j))
                            (r (adt-nrec s r)) (a (adt-nmap s a)))
                 (:instance adt-kreplace-nmap)))))

(in-theory (disable adt-nkcorr adt-nkempty-c adt-nkmem-c adt-nkfind-c adt-nkinsert-c
                    adt-nkremove-c adt-nkreplace-c))

(deftheory adt-nkinstance-unfold
  '(adt-nkempty-c adt-nkmem-c adt-nkfind-c adt-nkinsert-c adt-nkremove-c adt-nkreplace-c
    adt-nunrec adt-nrec
    (:executable-counterpart adt-nflat) (:executable-counterpart adt-flat-index)))

(defthm adt-true-listp-when-nval-ks
  (implies (adt-nval :ks s r) (true-listp r))
  :hints (("Goal" :induct (len s) :expand ((adt-nval :ks s r)))))

(defthm adt-true-listp-kfind-when-nseq-p
  (implies (adt-nseq-p s a) (true-listp (adt-kfind j k a))))
