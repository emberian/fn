; Witnesses and teeth for books/nntp-compress-dict (NNT-055's decisions,
; lanes compress-4 and compress-5): a payload stored under baseline 1 for a
; peer that holds baseline 1, for one that does not, over the empty
; dictionary; the body's escape and round trip; the request's parse; the
; capability line.
(in-package "ACL2")
(include-book "../../books/nntp-compress-dict")
(include-book "must-fail-checked")

;; lane compress-5: the choice is over the store's answer (DICT C N).
(defconst *cdt-d1* *fn-lzd-baseline-1-blake3*)
(defconst *cdt-other* (make-list 32 :initial-element 7))
(defconst *cdt-stored* (list *fn-lzd-baseline-1* '(1 2 3) 5))
(defconst *cdt-stored-0* (list nil '(1 2 3) 5))

; KEYSTONES fn-zdn-choose-complete and fn-zdn-choose-stored-only-shared,
; reachable: the answer's dictionary is baseline 1, the table names its
; digest, the peer listed it, and the answer is stored under that digest,
; whose dictionary is the answer's.
(defthm cdt-stored-witness
  (and (equal (fn-zdn-digest-of-dict *fn-lzd-baseline-1*) *cdt-d1*)
       (member-equal *cdt-d1* (list *cdt-other* *cdt-d1*))
       (equal (fn-zdn-choose *cdt-stored* (list *cdt-other* *cdt-d1*))
              (list :stored *cdt-d1*))
       (equal (fn-zdn-dict-of-digest *cdt-d1*) *fn-lzd-baseline-1*))
  :hints (("Goal" :in-theory (enable fn-zdn-choose)))
  :rule-classes nil)

; fn-zdn-choose-complete without its membership hypothesis: the answer has
; a shipped digest (the retained hypotheses hold), the peer did not list
; it, and the answer is :decoded, not stored.
(defthm cdt-peer-without-the-dictionary
  (and (consp *cdt-stored*)
       (fn-zdn-digest-of-dict (car *cdt-stored*))
       (not (member-equal (fn-zdn-digest-of-dict (car *cdt-stored*)) (list *cdt-other*)))
       (equal (fn-zdn-choose *cdt-stored* (list *cdt-other*)) :decoded))
  :hints (("Goal" :in-theory (enable fn-zdn-choose)))
  :rule-classes nil)

(must-fail-checked
 (defthm cdt-complete-without-membership
   (implies (and (consp stored) (fn-zdn-digest-of-dict (car stored)))
            (equal (fn-zdn-choose stored digests)
                   (list :stored (fn-zdn-digest-of-dict (car stored)))))
   :hints (("Goal" :in-theory (enable fn-zdn-choose)))))

; The empty dictionary has no digest, and no answer is never stored.
(defthm cdt-decoded-witnesses
  (and (null (fn-zdn-digest-of-dict nil))
       (equal (fn-zdn-choose *cdt-stored-0* (list *cdt-d1*)) :decoded)
       (equal (fn-zdn-choose nil (list *cdt-d1*)) :decoded))
  :hints (("Goal" :in-theory (enable fn-zdn-choose)))
  :rule-classes nil)

; The body: the four critical octets escaped, lines of 128, and back.
(defconst *cdt-c* (append '(0 10 13 61 46 13 10 46) (make-list 300 :initial-element 200)))
(defthm cdt-body-witness
  (let ((lines (fn-zdn-body-lines *cdt-c*)))
    (and (equal (take 9 (car lines)) '(61 64 61 74 61 77 61 125 46))
         (equal (len lines) 3)
         (not (member-equal 10 (fn-zdn-join lines)))
         (not (member-equal 13 (fn-zdn-join lines)))
         (not (member-equal 0 (fn-zdn-join lines)))
         (equal (fn-zdn-unescape (fn-zdn-join lines)) *cdt-c*)))
  :rule-classes nil)

; The request: a message-id and the peer's digests in lower-case hex.
(defconst *cdt-mid* (fn-nntp-string-octets "<a@b.example>"))
(defthm cdt-request-witness
  (and (equal (fn-zdn-request (list *cdt-mid* (fn-zdn-hex *cdt-d1*)))
              (list :ask *cdt-mid* (list *cdt-d1*)))
       (equal (fn-zdn-request (list *cdt-mid*)) :syntax)
       (equal (fn-zdn-request (list *cdt-mid* (fn-nntp-string-octets "ABCD"))) :syntax)
       (equal (fn-zdn-request (list *cdt-mid* (take 62 (fn-zdn-hex *cdt-d1*)))) :syntax)
       (equal (fn-zdn-request (list (fn-nntp-string-octets "a@b") (fn-zdn-hex *cdt-d1*)))
              :syntax))
  :hints (("Goal" :in-theory (enable fn-zdn-request)))
  :rule-classes nil)

; The capability: XFN-DICT and baseline 1's digest, on a connection that
; may ask; none on one that may not.
(defthm cdt-capability-witness
  (and (equal (fn-zdn-capability-line)
              (append (fn-nntp-string-octets "XFN-DICT ") (fn-zdn-hex *cdt-d1*)))
       (equal (fn-zdn-capability-lines (list (fn-nntp-string-octets "VERSION 2")) t)
              (list (fn-nntp-string-octets "VERSION 2") (fn-zdn-capability-line)))
       (equal (fn-zdn-capability-lines (list (fn-nntp-string-octets "VERSION 2")) nil)
              (list (fn-nntp-string-octets "VERSION 2"))))
  :hints (("Goal" :in-theory (enable fn-zdn-capability-line)))
  :rule-classes nil)

; PRF-974 by name.  fn-zdn-body-round-trip (no hypothesis): cdt-body-witness
; above is its positive witness on a true list; on an improper list the
; round trip is the list's true-list-fix, not the value itself.
(assert-event
 (and (equal (fn-zdn-unescape (fn-zdn-join (fn-zdn-body-lines '(1 13 . 7))))
             (true-list-fix '(1 13 . 7)))
      (not (equal (true-list-fix '(1 13 . 7)) '(1 13 . 7)))))
; fn-zdn-request-shape.  Positive: a parsed request is (:ask MID DIGESTS)
; with a message-id token and one 32-octet digest per argument after it.
(defconst *cdt-ask-args* (list *cdt-mid* (fn-zdn-hex *cdt-d1*)))
(assert-event
 (let ((r (fn-zdn-request *cdt-ask-args*)))
   (and (not (equal r :syntax))
        (equal (car r) :ask)
        (fn-nntp-message-id-tokenp (cadr r))
        (consp (caddr r))
        (fn-zdn-digest-listp (caddr r))
        (equal (len (caddr r)) (len (cdr *cdt-ask-args*))))))
; The hypothesis removed: a request with no digest is :syntax, which is no
; (:ask ...).
(assert-event
 (with-guard-checking :none
  (let ((r (fn-zdn-request (list *cdt-mid*))))
    (and (equal r :syntax) (not (equal (car r) :ask))))))
(must-fail-checked
 (defthm cdt-request-shape-without-parsed
   (equal (car (fn-zdn-request args)) :ask)
   :rule-classes nil))
