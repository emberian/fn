; FNFD pathname codec witnesses and teeth.
(in-package "ACL2")
(include-book "../../books/feed-filename")

(defconst *ff-safe* '(105 110 110))                 ; inn
(defconst *ff-v1-safe* '(118 49))                   ; v1
(defconst *ff-slash* '(46 46 47 101 115 99 97 112 101)) ; ../escape
(defconst *ff-dot* '(46 46))
(defconst *ff-safe-layout* (fn-feed-filename-layout *ff-safe*))
(defconst *ff-slash-layout* (fn-feed-filename-layout *ff-slash*))

; Existing safe journals are preserved byte for byte as feed/inn.fnfd.
(assert-event (equal *ff-safe-layout* '(:legacy ((105 110 110 46 102 110 102 100)))))
(assert-event (equal (fn-feed-filename-from-components
                      (fn-feed-filename-components *ff-safe*))
                     *ff-safe*))
; A safe peer literally named v1 is a sibling leaf (`v1.fnfd`), never the
; directory namespace used by encoded v1 peers.
(assert-event (equal (fn-feed-filename-components *ff-v1-safe*)
                     '((118 49 46 102 110 102 100))))
; A traversal-shaped peer cannot name a legacy path.  It gets a v1 component
; sequence whose payload is distinct from `escape', so neither traversal nor
; a filename collision can select the other peer's journal.
(assert-event (equal *ff-slash-layout*
                     '(:v1 ((118 49) (50 101 50 101 50 102 54 53 55 51 54 51 54 49 55 48 54 53)
                            (106 111 117 114 110 97 108 46 102 110 102 100)))))
(assert-event (not (equal (fn-feed-filename-components *ff-slash*)
                          (fn-feed-filename-components '(101 115 99 97 112 101)))))
(assert-event (equal (fn-feed-filename-from-components
                      (fn-feed-filename-components *ff-slash*))
                     *ff-slash*))
(assert-event (not (equal (fn-feed-filename-components *ff-v1-safe*)
                          (fn-feed-filename-components *ff-slash*))))
(assert-event (equal (car (fn-feed-filename-layout *ff-dot*)) :v1))
(assert-event (equal (fn-feed-filename-layout '(255)) '(:refused :peer-name)))
; Teeth for the injectivity theorem's input domain: non-ASCII input is refused
; before encoding, while two valid names differing at one byte have distinct
; encodings.  The length theorem also catches a lost or added hex half.
(assert-event (equal (fn-feed-filename-components '(255)) :bad))
(assert-event (equal (fn-feed-filename-from-components
                      '((118 49) (50) (106 111 117 114 110 97 108 46 102 110 102 100)))
                     :bad))
(defun ff-repeat (n octet)
  (if (zp n) nil (cons octet (ff-repeat (1- n) octet))))
(defconst *ff-deep* (ff-repeat 256 65))
(assert-event (equal *fn-ff-max-v1-chunks* 5))
(assert-event (equal *fn-ff-max-components* 7))
(assert-event (equal (fn-feed-filename-observation-limit) 8192))
; The budget is one total counter, so an empty directory may be observed at
; zero but the next retained name cannot be assigned a fresh local allowance.
(assert-event (equal (fn-feed-filename-observation-remaining 4 1) 3))
(assert-event (equal (fn-feed-filename-observation-remaining 0 0) 0))
(assert-event (equal (fn-feed-filename-observation-remaining 0 1) :bad))
(assert-event (equal (fn-feed-filename-observation-remaining 4 5) :bad))
(assert-event (equal (len (fn-feed-filename-components *ff-deep*)) 7))
(assert-event (equal (fn-feed-filename-from-components
                      (fn-feed-filename-components *ff-deep*))
                     *ff-deep*))
(assert-event (equal (len (fn-feed-filename-hex *ff-slash*))
                     (* 2 (len *ff-slash*))))
(assert-event (not (equal (fn-feed-filename-hex '(97 47 98))
                          (fn-feed-filename-hex '(97 95 98)))))
