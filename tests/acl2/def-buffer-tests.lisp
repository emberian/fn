; What `def-buffer' generates (books/def-buffer.lisp).
;
; 1. The expansion of `(def-buffer fn-octets-pg)' is, form for form, the
;    `defabsstobj' books/pagestore-words.lisp wrote out by hand before the
;    generator (quoted below as it stood at 0566eef95): the generator
;    replaced the twin without changing what the page store's digest buffer is.
; 2. A fresh instance runs: append a little-endian word, read it back as the
;    word, as the octets, and through the congruent `fn-octets' reader
;    (a function over `fn-octets' is applied to the clone).
; 3. Teeth: a different clone name changes every export (the expansion is not
;    a constant), and the generated row names the instance.
(in-package "ACL2")
(include-book "../../books/def-buffer")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(assert!
 (equal (def-buffer-expansion 'fn-octets-pg)
        '(defabsstobj fn-octets-pg
           :foundation fn-octets$c
           :recognizer (fn-octets-pg-p :logic fn-octets$ap :exec fn-octets$cp)
           :creator (create-fn-octets-pg :logic create-fn-octets$a :exec create-fn-octets$c)
           :exports ((fn-octets-pg-len :logic fn-octets$a-len :exec fn-octets$c-len)
                     (fn-octets-pg-get :logic fn-octets$a-get :exec fn-octets$c-get)
                     (fn-octets-pg-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
                     (fn-octets-pg-append-octet :logic fn-octets$a-append-octet
                                                :exec fn-octets$c-append-octet :protect t)
                     (fn-octets-pg-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
                     (fn-octets-pg-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                           :protect t)
                     (fn-octets-pg-list :logic fn-octets$a-list :exec fn-octets$c-list)
                     (fn-octets-pg-from-list :logic fn-octets$a-from-list
                                             :exec fn-octets$c-from-list :protect t)
                     (fn-octets-pg-append-list :logic fn-octets$a-append-list
                                               :exec fn-oct-write-list :protect t)
                     (fn-octets-pg-append-back :logic fn-octets$a-append-back
                                               :exec fn-octets$c-append-back :protect t)
                     (fn-octets-pg-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
                     (fn-octets-pg-append-word :logic fn-octets$a-append-word
                                               :exec fn-octets$c-append-word :protect t))
           :congruent-to fn-octets)))

(def-buffer dbt-buf :view t)

(defun dbt-run ()
  (with-local-stobj dbt-buf
    (mv-let (r dbt-buf)
      (let* ((dbt-buf (dbt-buf-clear dbt-buf))
             (dbt-buf (dbt-buf-append-word #x0807060504030201 8 dbt-buf)))
        (mv (list (dbt-buf-get-word 0 8 dbt-buf) (dbt-buf-get 0 dbt-buf) (dbt-buf-get 7 dbt-buf)
                  (dbt-buf-len dbt-buf) (dbt-buf-get-word 0 4 dbt-buf))
            dbt-buf))
      r)))

(assert! (equal (dbt-run) (list #x0807060504030201 1 8 8 #x04030201)))

; congruence: a function over fn-octets takes the clone
(defun dbt-len-via-fn-octets (fn-octets) (declare (xargs :stobjs fn-octets)) (fn-octets-len fn-octets))
(assert! (equal (dbt-len-via-fn-octets dbt-buf) 0))

; teeth: the expansion follows the name, and the word read is not the big-endian one.
(assert! (not (equal (def-buffer-expansion 'fn-octets-pg) (def-buffer-expansion 'dbt-buf))))
(assert! (not (equal (car (dbt-run)) #x0102030405060708)))
