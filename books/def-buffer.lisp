; fn: `def-buffer' --- a live octet buffer, one declaration.
;
;   (def-buffer NAME [:view t])
;
; adds NAME, an abstract stobj congruent to `fn-octets' (books/octets-stobj.lisp):
; the same flat (unsigned-byte 8) array and fill, the same logical value (the
; octet list), under its own live object, so a host worker's page buffer, a
; codec's output and the page store's digest buffer never share storage and
; all of them satisfy every theorem proved of `fn-octets'.  The exports are the
; twelve a codec clone reads, NAME-{len, get, put, append-octet, clear,
; reserve, list, from-list, append-list, append-back, get-word, append-word},
; each the `fn-octets' logic and executable under the new name (`get-word' and
; `append-word' the little-endian K-octet word at I / the word appended).
; `:view t' also states the logical view opened, as books/octets-stobj.lisp
; does for `fn-octets': NAME-p is an octet list, clear is nil, list is the
; value, len is `len', get-word is `fn-oct-word-at', append-word is `append'
; of `fn-oct-word-octets'.
; Nothing is proved here: the correspondence and guard obligations belong to
; `fn-octets' and `:congruent-to' reuses them; what is generated is the clone
; the tree used to write out by hand (25 copies, books/pagestore-words.lisp
; `fn-octets-pg' the first).  A row in the world table `fn-generated' names
; the instance.
;
; Distinct from `def-representation''s `:octet-seq' (a representation with its
; own foundation and a generated schema): def-buffer is the buffer whose
; exports are `fn-octets''s own, for code written against them.
(in-package "ACL2")
(include-book "octets-stobj")

(defun def-buffer-sym (name suffix)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name name) suffix) name))

(defun def-buffer-creator (name)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (concatenate 'string "CREATE-" (symbol-name name)) name))

(defun def-buffer-expansion (name)
  (declare (xargs :mode :program))
  (let ((n name))
    `(defabsstobj ,name
       :foundation fn-octets$c
       :recognizer (,(def-buffer-sym n "-P") :logic fn-octets$ap :exec fn-octets$cp)
       :creator (,(def-buffer-creator n) :logic create-fn-octets$a :exec create-fn-octets$c)
       :exports ((,(def-buffer-sym n "-LEN") :logic fn-octets$a-len :exec fn-octets$c-len$inline)
                 (,(def-buffer-sym n "-GET") :logic fn-octets$a-get :exec fn-octets$c-get$inline)
                 (,(def-buffer-sym n "-PUT") :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
                 (,(def-buffer-sym n "-APPEND-OCTET") :logic fn-octets$a-append-octet
                                       :exec fn-octets$c-append-octet$inline :protect t)
                 (,(def-buffer-sym n "-CLEAR") :logic fn-octets$a-clear :exec fn-octets$c-clear)
                 (,(def-buffer-sym n "-RESERVE") :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                  :protect t)
                 (,(def-buffer-sym n "-LIST") :logic fn-octets$a-list :exec fn-octets$c-list)
                 (,(def-buffer-sym n "-FROM-LIST") :logic fn-octets$a-from-list
                                    :exec fn-octets$c-from-list :protect t)
                 (,(def-buffer-sym n "-APPEND-LIST") :logic fn-octets$a-append-list
                                      :exec fn-oct-write-list :protect t)
                 (,(def-buffer-sym n "-APPEND-BACK") :logic fn-octets$a-append-back
                                      :exec fn-octets$c-append-back :protect t)
                 (,(def-buffer-sym n "-GET-WORD") :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
                 (,(def-buffer-sym n "-APPEND-WORD") :logic fn-octets$a-append-word
                                      :exec fn-octets$c-append-word$inline :protect t))
       :congruent-to fn-octets)))

; `:view t' adds the logical view, opened, as books/octets-stobj.lisp states it for `fn-octets':
; the value is the octet list, so the exports are list terms.  Left enabled as
; rewrite rules with the exports themselves disabled (the theory the page
; store's clone already ran in).
(defun def-buffer-view (name)
  (declare (xargs :mode :program))
  (let ((n name))
    `((defthm ,(def-buffer-sym n "-P-IS-OCTET-LISTP")
        (equal (,(def-buffer-sym n "-P") x) (fn-cbor-octet-listp x))
        :hints (("Goal" :in-theory (enable ,(def-buffer-sym n "-P")))))
      (defthm ,(def-buffer-sym n "-CLEAR-IS-NIL")
        (equal (,(def-buffer-sym n "-CLEAR") ,n) nil)
        :hints (("Goal" :in-theory (enable ,(def-buffer-sym n "-CLEAR")))))
      (defthm ,(def-buffer-sym n "-LIST-IS-IDENTITY")
        (equal (,(def-buffer-sym n "-LIST") ,n) ,n)
        :hints (("Goal" :in-theory (enable ,(def-buffer-sym n "-LIST")))))
      (defthm ,(def-buffer-sym n "-LEN-IS-LEN")
        (equal (,(def-buffer-sym n "-LEN") ,n) (len ,n))
        :hints (("Goal" :in-theory (enable ,(def-buffer-sym n "-LEN")))))
      (defthm ,(def-buffer-sym n "-GET-WORD-IS-WORD-AT")
        (equal (,(def-buffer-sym n "-GET-WORD") i k ,n) (fn-oct-word-at i k ,n))
        :hints (("Goal" :in-theory (enable ,(def-buffer-sym n "-GET-WORD")))))
      (defthm ,(def-buffer-sym n "-APPEND-WORD-IS-APPEND")
        (equal (,(def-buffer-sym n "-APPEND-WORD") w k ,n)
               (append ,n (fn-oct-word-octets w k)))
        :hints (("Goal" :in-theory (enable ,(def-buffer-sym n "-APPEND-WORD")))))
      (in-theory (disable ,(def-buffer-sym n "-P") ,(def-buffer-sym n "-CLEAR")
                          ,(def-buffer-sym n "-LIST") ,(def-buffer-sym n "-LEN")
                          ,(def-buffer-sym n "-GET-WORD") ,(def-buffer-sym n "-APPEND-WORD"))))))

(defmacro def-buffer (name &key view)
  `(progn
     ,(def-buffer-expansion name)
     ,@(and view (def-buffer-view name))
     (table fn-generated ',name '(:def-buffer :congruent-to fn-octets :view ,view))))
