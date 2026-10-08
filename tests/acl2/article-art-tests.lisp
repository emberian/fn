; PRF-1359: exact ART split/roundtrip, with boundary and domain teeth.
(in-package "ACL2")
(include-book "../../books/article-art")
(include-book "must-fail-checked")

(defconst *art-test-x* '(88 58 32 97 13 10 13 10 65 13 10 13 10 66 0 255 0))
(defconst *art-test-head* '(88 58 32 97 13 10 13 10))
(defconst *art-test-body* '(65 13 10 13 10 66 0 255 0))

(assert-event
 (and (fn-bch-octetsp *art-test-x*)
      (mv-let (head body) (fn-art-split *art-test-x*)
        (and (equal head *art-test-head*)
             (equal body *art-test-body*)
             (equal (append head body) *art-test-x*)
             (true-listp head)
             (fn-art-first-separator-headp head)))
      (equal (fn-art-octets (fn-art-of *art-test-x*)) *art-test-x*)
      (fn-art-headp (fn-art-of *art-test-x*))))

; A last-separator mutation still recomposes, but violates the location.
(must-fail-checked
 (assert-event
  (let ((head '(88 58 32 97 13 10 13 10 65 13 10 13 10))
        (body '(66 0 255 0)))
    (and (fn-bch-octetsp *art-test-x*)
         (equal (append head body) *art-test-x*)
         (fn-art-first-separator-headp head)))))

; Removing the octet premise cannot promise equality to an ACL2 atom.
(must-fail-checked
 (assert-event
  (mv-let (head body) (fn-art-split 7)
    (equal (append head body) 7))))
(must-fail-checked
 (assert-event (equal (fn-art-octets (fn-art-of 7)) 7)))
(must-fail-checked
 (assert-event
  (let ((x '(88 58 32 97 13 10 13 10 :bad)))
    (equal (fn-art-octets (fn-art-of x)) x))))

; Empty header, no separator, empty article and trailing zero are distinct.
(assert-event
 (and (equal (fn-art-of '(13 10 0)) (cons '(13 10) 256))
      (fn-art-headp (fn-art-of '(13 10 0)))
      (equal (fn-art-octets (fn-art-of '(13 10 0))) '(13 10 0))
      (equal (fn-art-of '(88 13 10)) (cons '(88 13 10) 1))
      (fn-art-headp (fn-art-of '(88 13 10)))
      (equal (fn-art-of nil) (cons nil 1))
      (fn-art-headp (fn-art-of nil))))

; Omitting the sentinel loses the final zero octets.
(must-fail-checked
 (assert-event
  (equal (fn-bch-unpack 0) '(0))))

(include-book "../../books/defkeystone")

(defteeth fn-art-split-recomposes
  :claim (((octets (fn-bch-octetsp x)))
          (mv-let (head body) (fn-art-split x)
            (and (equal (append head body) x)
                 (or (and (true-listp head)
                          (fn-art-first-separator-headp head))
                     (equal body nil)))))
  :subject fn-art-split
  :witness ((x '(88 58 32 97 13 10 13 10 65 13 10 13 10 66)))
  :breaks ((octets ((x 7))))
  :mutations
  ((last-separator
    (:conclusion
     (mv-let (head body) (fn-art-split x)
       (and (equal (append head body) x)
            (equal head '(88 58 32 97 13 10 13 10 65 13 10 13 10)))))
    ((x '(88 58 32 97 13 10 13 10 65 13 10 13 10 66)))
    :fault "Selecting the body's later separator still recomposes but moves body octets into HEAD.")))

(defteeth fn-art-of-roundtrip
  :claim (((octets (fn-bch-octetsp x)))
          (and (equal (fn-art-octets (fn-art-of x)) x)
               (fn-art-headp (fn-art-of x))))
  :subject fn-art-of
  :witness ((x '(88 58 32 97 13 10 13 10 65 0 255 0)))
  :breaks ((octets ((x 7))))
  :mutations
  ((body-lost
    (:conclusion
     (and (equal (fn-art-octets (cons (fn-art-head (fn-art-of x)) 1)) x)
          (fn-art-headp (fn-art-of x))))
    ((x '(88 58 32 97 13 10 13 10 65 0 255 0)))
    :fault "Replacing the packed body with the empty sentinel loses its exact bytes.")))
