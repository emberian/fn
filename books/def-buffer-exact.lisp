; def-buffer's charged-ownership extension: exact array size, physical clear.
; Scratch-buffer exports and their amortized growth remain in def-buffer.
(in-package "ACL2")
(include-book "def-buffer")
(include-book "octet-buffer-exact")
(defmacro def-buffer-exact (name)
  `(progn
     (defabsstobj ,name
       :foundation fn-obe$c
       :recognizer (,(def-buffer-sym name "-P") :logic fn-obe$ap :exec fn-obe$cp)
       :creator (,(def-buffer-creator name) :logic create-fn-obe$a :exec create-fn-obe$c)
       :exports ((,(def-buffer-sym name "-LEN") :logic fn-obe$a-len :exec fn-obe$c-len)
                 (,(def-buffer-sym name "-GET") :logic fn-obe$a-get :exec fn-obe$c-get)
                 (,(def-buffer-sym name "-PUT") :logic fn-obe$a-put :exec fn-obe$c-put :protect t)
                 (,(def-buffer-sym name "-CLEAR") :logic fn-obe$a-clear :exec fn-obe$c-clear :protect t)
                 (,(def-buffer-sym name "-RESIZE") :logic fn-obe$a-resize :exec fn-obe$c-resize :protect t))
       :congruent-to fn-obe)
     (defthm ,(def-buffer-sym name "-P-IS-OCTETS")
       (equal (,(def-buffer-sym name "-P") x) (fn-cbor-octet-listp x)))
     (defthm ,(def-buffer-sym name "-LEN-IS-LEN")
       (equal (,(def-buffer-sym name "-LEN") ,name) (len ,name)))
     (defthm ,(def-buffer-sym name "-GET-IS-NTH")
       (equal (,(def-buffer-sym name "-GET") i ,name) (nth i ,name)))
     (defthm ,(def-buffer-sym name "-CLEAR-IS-NIL")
       (equal (,(def-buffer-sym name "-CLEAR") ,name) nil))
     (table fn-generated ',name '(:def-buffer-exact :congruent-to fn-obe))))
