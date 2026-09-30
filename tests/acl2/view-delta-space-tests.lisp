(in-package "ACL2")
(include-book "../../books/view-delta-space")

; Exact host-updater cons count: each new character contributes a spine
; and an entry; the terminal contributes those two plus the aggregate pair.
(defconst *vcst-key* (coerce (make-list 256 :initial-element #\a) 'string))
(defconst *vcst-pair* '(1 . 7))
(defconst *vcst-trie* (fn-vdc-put *vcst-key* *vcst-pair* nil))
(assert-event (and (fn-vd-pairp *vcst-pair*)
                  (equal (length *vcst-key*) 256)
                  (equal (fn-vcs-conses *vcst-trie*) 515)
                  (<= (fn-vcs-conses *vcst-trie*)
                      (+ (* 2 (length *vcst-key*)) 3 (fn-vcs-conses nil)))))
; An update to an existing key reuses the same result shape, and retraction
; deliberately keeps a zero terminal until the funded rebuild.
(assert-event
 (and (equal (fn-vcs-conses (fn-vdc-bump *vcst-key* 5 *vcst-trie*)) 515)
      (equal (fn-vcs-conses (fn-vdc-unbump *vcst-key* 7 *vcst-trie*)) 515)
      (equal (fn-vdc-get *vcst-key* (fn-vdc-unbump *vcst-key* 7 *vcst-trie*)) '(0 . 0))))
; Hypothesis removal: a non-pair payload costs more than the one pair cell.
(assert-event
 (let ((pair '(1 2 3)) (key "a") (trie nil))
   (and (not (fn-vd-pairp pair))
        (not (<= (fn-vcs-conses (fn-vdc-put key pair trie))
                 (+ (* 2 (length (if (stringp key) key ""))) 3
                    (fn-vcs-conses trie)))))))
; Shared prefix, distinct leaves: no quadratic retained tree accumulation.
(assert-event
 (let* ((one (fn-vdc-put "aa" '(1 . 7) nil))
        (two (fn-vdc-put "ab" '(1 . 9) one)))
   (and (equal (fn-vcs-conses one) 7)
        (equal (fn-vcs-conses two) 12)
        (equal (fn-vdc-get "aa" two) '(1 . 7))
        (equal (fn-vdc-get "ab" two) '(1 . 9)))))

; Cold fold boundary, with a nonempty seed and shared-prefix contributions.
(assert-event
 (let* ((cs '(("aa" . 7) ("ab" . 9)))
        (trie (fn-vdc-put "seed" '(1 . 2) nil)))
   (and (fn-vdc-contribsp cs)
        (<= (fn-vcs-conses (fn-vdc-build-loop cs trie))
            (+ (* 2 (fn-vcs-key-characters cs)) (* 3 (len cs))
               (fn-vcs-conses trie))))))
