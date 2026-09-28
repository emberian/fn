; fn: witnesses for books/state-digest.lisp (lane proto-determinism).
;
; The digest is a comparison tool (`store ROOT digest'): two opens of one
; history must print the same lines, and two different states should not.
; No theorem here: what the witnesses show, by evaluation, is that the
; encoding separates the values a naive printer would confuse (a dotted
; pair and a list, a string, a symbol and a character, a ratio and a
; complex, NIL and "NIL", symbols of two packages), that it is the value and
; not the layout that is digested (a list built two ways), and that the
; entries the host calls are guard-verified.  Nothing bears on collision
; resistance (A-CRYPTO).

(in-package "ACL2")
(include-book "../../books/state-digest")
; The store's digest executes through its attachment.
(include-book "../../books/crypto-attach")

(assert-event
 (equal (list (symbol-class 'fn-sdg-digest (w state))
              (symbol-class 'fn-sdg-arena-pool (w state))
              (symbol-class 'fn-sdg-rows-history (w state))
              (symbol-class 'fn-sdg-hex (w state)))
        '(:common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant)))

; The exact octets of one small value: a list of an integer, a negative
; integer, a string and a character, terminated by NIL.
(assert-event
 (equal (fn-sdg-canon '(1 -300 "ab" #\c))
        '(76 73 0 1 73 1 172 2 83 2 97 98 67 99 69
          89 83 11 67 79 77 77 79 78 45 76 73 83 80 83 3 78 73 76)))

; Values a printer might confuse encode differently.
(defun fn-sdg-canon-each (xs)
  (declare (xargs :mode :program))
  (if (atom xs) nil (cons (fn-sdg-canon (car xs)) (fn-sdg-canon-each (cdr xs)))))

(defun fn-sdg-test-distinct (xs)
  (declare (xargs :mode :program))
  (or (atom xs)
      (and (not (member-equal (fn-sdg-canon (car xs))
                              (fn-sdg-canon-each (cdr xs))))
           (fn-sdg-test-distinct (cdr xs)))))

(assert-event
 (fn-sdg-test-distinct
  (list '(1 . 2) '(1 2) '((1) 2) '(1 (2))
        "a" 'a #\a :a "A" nil "NIL" 'nil-not '(nil) 0 1/2 #c(1/2 1) -1/2
        128 127 -128 256 (expt 2 64) (- (expt 2 64))
        'acl2::car 'common-lisp::cons "" '("") '(""  . ""))))

; The digest is of the value: a list consed two ways digests alike, and a
; one-element change does not.
(assert-event
 (let ((a (append '(1 2) '(3 4)))
       (b (list 1 2 3 4)))
   (and (equal (fn-sdg-digest a) (fn-sdg-digest b))
        (not (equal (fn-sdg-digest a) (fn-sdg-digest '(1 2 3 5))))
        (equal (len (fn-sdg-digest a)) 32))))

; LEB128: 127 is one octet, 128 two, 300 is (172 2).
(assert-event
 (and (equal (fn-sdg-leb 127 nil) '(127))
      (equal (revappend (fn-sdg-leb 128 nil) nil) '(128 1))
      (equal (revappend (fn-sdg-leb 300 nil) nil) '(172 2))))

(assert-event
 (equal (fn-sdg-hex '(0 15 16 255)) '(48 48 48 102 49 48 102 102)))
