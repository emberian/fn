; Witnesses and teeth for books/nntp-compress-dict (NNT-055's decisions,
; lane compress-4): a stored frame over baseline 1 for a peer that holds
; baseline 1, for one that does not, over the empty dictionary, and a
; payload that is no frame; the request's parse; the capability line.
(in-package "ACL2")
(include-book "../../books/nntp-compress-dict")
(include-book "must-fail-checked")

(defconst *cdt-d1* *fn-lzd-baseline-1-blake3*)
(defconst *cdt-other* (make-list 32 :initial-element 7))
(defconst *cdt-frame* (fn-lzr-frame *fn-lzd-baseline-1-id* 0 5 nil '(1 2 3)))
(defconst *cdt-frame-0* (fn-lzr-frame 0 0 5 nil '(1 2 3)))

; KEYSTONES fn-zdn-choose-complete and fn-zdn-choose-stored-only-shared,
; reachable: the frame parses, the table records baseline 1's digest for
; its DICT-ID, the peer listed it, and the answer is the stored frame under
; that digest.
(defthm cdt-stored-witness
  (let ((f (fn-lzr-parse *cdt-frame*)))
    (and f
         (equal (fn-zdn-digest-of-id (car f)) *cdt-d1*)
         (member-equal *cdt-d1* (list *cdt-other* *cdt-d1*))
         (equal (fn-zdn-choose *cdt-frame* (list *cdt-other* *cdt-d1*))
                (list :stored *cdt-d1*))))
  :hints (("Goal" :in-theory (enable fn-zdn-choose)))
  :rule-classes nil)

; fn-zdn-choose-complete without its membership hypothesis: the frame
; parses and has a shipped digest (both retained hypotheses hold), the peer
; did not list it, and the answer is :decoded, not stored.
(defthm cdt-peer-without-the-dictionary
  (let ((f (fn-lzr-parse *cdt-frame*)))
    (and f
         (fn-zdn-digest-of-id (car f))
         (not (member-equal (fn-zdn-digest-of-id (car f)) (list *cdt-other*)))
         (equal (fn-zdn-choose *cdt-frame* (list *cdt-other*)) :decoded)))
  :hints (("Goal" :in-theory (enable fn-zdn-choose)))
  :rule-classes nil)

(must-fail-checked
 (defthm cdt-complete-without-membership
   (implies (and (fn-lzr-parse z) (fn-zdn-digest-of-id (car (fn-lzr-parse z))))
            (equal (fn-zdn-choose z digests)
                   (list :stored (fn-zdn-digest-of-id (car (fn-lzr-parse z))))))
   :hints (("Goal" :in-theory (enable fn-zdn-choose)))))

; Without a shipped digest (the empty dictionary, ID 0) or without a frame,
; the answer is :decoded whatever the peer lists.
(defthm cdt-decoded-witnesses
  (and (fn-lzr-parse *cdt-frame-0*)
       (null (fn-zdn-digest-of-id 0))
       (equal (fn-zdn-choose *cdt-frame-0* (list *cdt-d1*)) :decoded)
       (null (fn-lzr-parse '(1 2 3)))
       (equal (fn-zdn-choose '(1 2 3) (list *cdt-d1*)) :decoded))
  :hints (("Goal" :in-theory (enable fn-zdn-choose)))
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
