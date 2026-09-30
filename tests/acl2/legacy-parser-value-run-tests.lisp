(in-package "ACL2")
(include-book "../../books/legacy-parser-value-run")

(defconst *lpvrt-name* '(83 117 98 106 101 99 116))
(defconst *lpvrt-value* '(32 120 9 121))
(defconst *lpvrt-line* (append *lpvrt-name* (cons 58 (append *lpvrt-value* '(13 10)))))
(defconst *lpvrt-state* (fn-nlv-run *lpvrt-line* (fn-lpc-header-begin) 0 0 :pin))

; Full literal antecedents and conclusions for the new-field source-value,
; selected-name and completed-span theorems, reached from begin.
(defthm lpvrt-new-field-positive
  (let* ((s (fn-lpc-header-begin)) (source nil)
         (name *lpvrt-name*) (bytes *lpvrt-value*) (line *lpvrt-line*)
         (out (fn-nlv-run line s (len source) 0 :pin)))
    (and (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
         (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
         (fn-article-namep name) (fn-article-header-bytes-p bytes)
         (consp bytes) (fn-article-wspp (car bytes))
         (<= (+ (len name) 1 (len bytes)) *fn-article-max-line-octets*)
         (fn-lpv-value-state-p out (append source line) bytes)
         (equal (fn-lpc-at 6 out)
                (fn-lpc-name-key (fn-lpc-names-scan *fn-lpc-names* name)))
         (equal (fn-lpc-at 8 out) (fn-lpc-close-fields s 0 :pin))
         (equal (fn-nov-scrub (fn-lpv-slice (append source line)
                                          (fn-lpc-at 4 out) (fn-lpc-at 5 out)))
                (fn-nov-scrub (fn-nov-value-content bytes)))
         (equal (fn-nov-scrub (fn-nov-value-content bytes)) '(120 32 121))))
  :rule-classes nil)

(defthm lpvrt-fold-line-positive
  (let* ((s *lpvrt-state*) (source *lpvrt-line*) (value *lpvrt-value*)
         (bytes '(32 122 32))
         (out (fn-nlv-run (append bytes '(13 10)) s (len source) 0 :pin)))
    (and (fn-lpv-value-state-p s source value)
         (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
         (fn-lpc-at 2 s) (fn-article-header-bytes-p bytes)
         (fn-article-wspp (car bytes)) (fn-article-has-vcharp bytes)
         (<= (len bytes) *fn-article-max-line-octets*)
         (fn-lpv-value-state-p out (append source (append bytes '(13 10)))
                               (append value bytes))
         (equal (fn-lpc-at 6 out) (fn-lpc-at 6 s))
         (equal (fn-lpc-at 8 out) (fn-lpc-at 8 s))
         (equal (fn-nov-scrub
                 (fn-lpv-slice (append source (append bytes '(13 10)))
                               (fn-lpc-at 4 out) (fn-lpc-at 5 out)))
                (fn-nov-scrub (fn-nov-value-content (append value bytes))))
         (equal (fn-nov-scrub (fn-nov-value-content (append value bytes)))
                '(120 32 121 32 122 32))))
  :rule-classes nil)

; Removing the source/value correspondence while retaining every physical
; fold hypothesis breaks the normalized span equation (corrupted state).
(defthm lpvrt-fold-without-source-value-invariant
  (let* ((s (fn-lpc-put 4 1000 *lpvrt-state*))
         (source *lpvrt-line*) (value *lpvrt-value*) (bytes '(32 122 32))
         (out (fn-nlv-run (append bytes '(13 10)) s (len source) 0 :pin)))
    (and (not (fn-lpv-value-state-p s source value))
         (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
         (fn-lpc-at 2 s) (fn-article-header-bytes-p bytes)
         (fn-article-wspp (car bytes)) (fn-article-has-vcharp bytes)
         (<= (len bytes) *fn-article-max-line-octets*)
         (not (equal (fn-nov-scrub
                      (fn-lpv-slice (append source (append bytes '(13 10)))
                                    (fn-lpc-at 4 out) (fn-lpc-at 5 out)))
                     (fn-nov-scrub (fn-nov-value-content (append value bytes)))))))
  :rule-classes nil)

; A visible earlier field does not license an empty physical continuation.
; The span conclusion fails if the current fold's visible-byte premise goes.
(defthm lpvrt-fold-without-local-visible-byte
  (let* ((s *lpvrt-state*) (source *lpvrt-line*) (value *lpvrt-value*)
         (bytes '(32 9))
         (out (fn-nlv-run (append bytes '(13 10)) s (len source) 0 :pin)))
    (and (fn-lpv-value-state-p s source value)
         (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
         (fn-lpc-at 2 s) (fn-article-header-bytes-p bytes)
         (fn-article-wspp (car bytes)) (not (fn-article-has-vcharp bytes))
         (<= (len bytes) *fn-article-max-line-octets*)
         (not (equal (fn-nov-scrub
                      (fn-lpv-slice (append source (append bytes '(13 10)))
                                    (fn-lpc-at 4 out) (fn-lpc-at 5 out)))
                     (fn-nov-scrub (fn-nov-value-content (append value bytes)))))))
  :rule-classes nil)

; The source-prefix proper-list assumption was removed after a stronger
; proof. A dotted consumed prefix still has the same actual line result.
(defthm lpvrt-improper-source-prefix-positive
  (let* ((source '(1 2 . 99)) (s (fn-lpc-header-begin))
         (name *lpvrt-name*) (bytes *lpvrt-value*) (line *lpvrt-line*)
         (out (fn-nlv-run line s (len source) 0 :pin)))
    (and (not (true-listp source))
         (equal (fn-lpc-at 0 s) :start) (equal (fn-lpc-at 1 s) 0)
         (or (not (fn-lpc-at 2 s)) (fn-lpc-at 3 s))
         (fn-article-namep name) (fn-article-header-bytes-p bytes)
         (consp bytes) (fn-article-wspp (car bytes))
         (<= (+ (len name) 1 (len bytes)) *fn-article-max-line-octets*)
         (fn-lpv-value-state-p out (append source line) bytes)
         (equal (fn-nov-scrub (fn-lpv-slice (append source line)
                                          (fn-lpc-at 4 out) (fn-lpc-at 5 out)))
                (fn-nov-scrub (fn-nov-value-content bytes)))))
  :rule-classes nil)
