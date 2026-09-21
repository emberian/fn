; Persistent Message-ID trie for immutable committed article views.
(in-package "ACL2")
(include-book "acceptance")

; A trie is an association list. Character keys lead to child tries and the
; keyword key below holds the value at the end of a Message-ID. Character keys
; cannot collide with the keyword. Updates copy only one bounded character
; path, so older reader pins remain valid and memory grows with accepted input,
; not with the square of the number of committed versions.
(defconst *fn-midx-value-key* :fn-midx-value)

(defun fn-midx-branch-get (key branches)
  (declare (xargs :guard t))
  (if (consp branches)
      (if (equal key (fn-ag-car (fn-ag-car branches)))
          (fn-ag-cdr (fn-ag-car branches))
        (fn-midx-branch-get key (fn-ag-cdr branches)))
    nil))

(defun fn-midx-branch-put (key value branches)
  (declare (xargs :guard t))
  (if (consp branches)
      (if (equal key (fn-ag-car (fn-ag-car branches)))
          (cons (cons key value) (fn-ag-cdr branches))
        (cons (fn-ag-car branches)
              (fn-midx-branch-put key value (fn-ag-cdr branches))))
    (list (cons key value))))

(defun fn-midx-put-chars (characters article trie)
  (declare (xargs :guard t))
  (if (consp characters)
      (let ((key (fn-ag-car characters)))
        (fn-midx-branch-put
         key
         (fn-midx-put-chars
          (fn-ag-cdr characters) article (fn-midx-branch-get key trie))
         trie))
    (fn-midx-branch-put *fn-midx-value-key* article trie)))

(defun fn-midx-get-chars (characters trie)
  (declare (xargs :guard t))
  (if (consp characters)
      (fn-midx-get-chars
       (fn-ag-cdr characters)
       (fn-midx-branch-get (fn-ag-car characters) trie))
    (fn-midx-branch-get *fn-midx-value-key* trie)))

(defun fn-midx-key-chars (msgid)
  (declare (xargs :guard t))
  (if (stringp msgid) (coerce msgid 'list) nil))

(defun fn-midx-string-article-listp (articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (and (stringp (fn-article-msgid (fn-ag-car articles)))
           (fn-midx-string-article-listp (fn-ag-cdr articles)))
    (null articles)))

(defun fn-midx-extend (article trie)
  (declare (xargs :guard t))
  (fn-midx-put-chars (fn-midx-key-chars (fn-article-msgid article)) article trie))

(defun fn-midx-build (articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (fn-midx-extend (fn-ag-car articles) (fn-midx-build (fn-ag-cdr articles)))
    nil))

(defun fn-midx-lookup (msgid trie)
  (declare (xargs :guard t))
  (if (stringp msgid)
      (fn-midx-get-chars (fn-midx-key-chars msgid) trie)
    nil))

(defun fn-midx-correspondencep (trie articles)
  (declare (xargs :guard t))
  (equal trie (fn-midx-build articles)))

(defthm fn-midx-branch-get-of-put
  (equal (fn-midx-branch-get wanted
                             (fn-midx-branch-put key value branches))
         (if (equal wanted key)
             value
           (fn-midx-branch-get wanted branches)))
  :hints (("Goal" :induct (fn-midx-branch-put key value branches))))

(defthm fn-midx-get-chars-of-put-other-branch
  (implies (and (consp wanted)
                (not (equal (fn-ag-car wanted) key)))
           (equal (fn-midx-get-chars wanted
                                     (fn-midx-branch-put key value trie))
                  (fn-midx-get-chars wanted trie)))
  :hints (("Goal" :expand ((fn-midx-get-chars wanted
                                               (fn-midx-branch-put key value trie))
                             (fn-midx-get-chars wanted trie)))))

(defthm fn-midx-get-chars-of-put-same-branch
  (equal (fn-midx-get-chars (cons key rest)
                             (fn-midx-branch-put key value trie))
         (fn-midx-get-chars rest value))
  :hints (("Goal" :expand ((fn-midx-get-chars (cons key rest)
                                               (fn-midx-branch-put key value trie))))))

(defthm fn-midx-character-is-not-value-key
  (implies (characterp ch)
           (not (equal ch *fn-midx-value-key*))))

(defthm fn-midx-value-of-put-character
  (implies (characterp ch)
           (equal (fn-midx-branch-get *fn-midx-value-key*
                                      (fn-midx-branch-put ch value trie))
                  (fn-midx-branch-get *fn-midx-value-key* trie))))

(defthm fn-midx-get-chars-of-put-value
  (implies (and (consp wanted) (character-listp wanted))
           (equal (fn-midx-get-chars
                   wanted (fn-midx-branch-put *fn-midx-value-key* value trie))
                  (fn-midx-get-chars wanted trie))))

(defun fn-midx-lookup-put-induct (wanted characters article trie)
  (declare (xargs :guard t))
  (if (and (consp wanted) (consp characters)
           (equal (fn-ag-car wanted) (fn-ag-car characters)))
      (fn-midx-lookup-put-induct
       (fn-ag-cdr wanted) (fn-ag-cdr characters) article
       (fn-midx-branch-get (fn-ag-car characters) trie))
    (list wanted characters article trie)))

(defthm fn-midx-get-chars-of-put-chars
  (implies (and (character-listp wanted)
                (character-listp characters))
           (equal (fn-midx-get-chars wanted
                            (fn-midx-put-chars characters article trie))
         (if (equal wanted characters)
             article
           (fn-midx-get-chars wanted trie))))
  :hints (("Goal" :induct (fn-midx-lookup-put-induct wanted characters article trie)
           :in-theory (disable fn-midx-branch-get fn-midx-branch-put))))

(defthm fn-midx-get-chars-of-nil
  (implies (character-listp characters)
           (equal (fn-midx-get-chars characters nil) nil))
  :hints (("Goal" :induct (fn-midx-get-chars characters nil))))

(defthm fn-midx-equal-lists-have-equal-string-coercions
  (implies (equal x y)
           (equal (coerce x 'string) (coerce y 'string))))

(defthm fn-midx-string-list-coercion-injective
  (implies (and (stringp a) (stringp b))
           (equal (equal (coerce a 'list) (coerce b 'list))
                  (equal a b)))
  :hints (("Goal"
           :use ((:instance coerce-inverse-2 (x a))
                 (:instance coerce-inverse-2 (x b))
                 (:instance fn-midx-equal-lists-have-equal-string-coercions
                            (x (coerce a 'list)) (y (coerce b 'list))))
           :in-theory (disable coerce-inverse-2))))

; Keystone: for arbitrary ordered valid article lists, including a synthetic
; duplicate witness, the trie returns the same first article as the canonical
; scan. Production acceptance itself excludes duplicate Message-IDs.
(defthm fn-midx-lookup-of-build-is-find-article
  (implies (and (stringp msgid)
                (fn-midx-string-article-listp articles))
           (equal (fn-midx-lookup msgid (fn-midx-build articles))
                  (fn-find-article msgid articles)))
  :hints (("Goal" :induct (fn-midx-build articles)
           :in-theory (enable fn-find-article))))

(defthm fn-midx-extend-preserves-correspondence
  (implies (fn-midx-correspondencep trie articles)
           (fn-midx-correspondencep
            (fn-midx-extend article trie)
            (cons article articles)))
  :hints (("Goal" :in-theory (enable fn-midx-correspondencep))))
