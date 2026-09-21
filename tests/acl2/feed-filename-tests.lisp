; FNFD pathname codec witnesses and teeth.
(in-package "ACL2")
(include-book "../../books/feed-filename")

(defconst *ff-safe* '(105 110 110))                 ; inn
(defconst *ff-slash* '(46 46 47 101 115 99 97 112 101)) ; ../escape
(defconst *ff-dot* '(46 46))
(defconst *ff-safe-layout* (fn-feed-filename-layout *ff-safe*))
(defconst *ff-slash-layout* (fn-feed-filename-layout *ff-slash*))

; Existing safe journals are preserved byte for byte as feed/inn.fnfd.
(assert-event (equal *ff-safe-layout* '(:legacy ((105 110 110 46 102 110 102 100)))))
; A traversal-shaped peer cannot name a legacy path.  It gets a v1 component
; sequence whose payload is distinct from `escape', so neither traversal nor
; a filename collision can select the other peer's journal.
(assert-event (equal *ff-slash-layout*
                     '(:v1 ((118 49) (50 101 50 101 50 102 54 53 55 51 54 51 54 49 55 48 54 53)
                            (106 111 117 114 110 97 108 46 102 110 102 100)))))
(assert-event (not (equal (fn-feed-filename-components *ff-slash*)
                          (fn-feed-filename-components '(101 115 99 97 112 101)))))
(assert-event (equal (car (fn-feed-filename-layout *ff-dot*)) :v1))
(assert-event (equal (fn-feed-filename-layout '(255)) '(:refused :peer-name)))
; Teeth for the injectivity theorem's input domain: non-ASCII input is refused
; before encoding, while two valid names differing at one byte have distinct
; encodings.  The length theorem also catches a lost or added hex half.
(assert-event (equal (fn-feed-filename-components '(255)) :bad))
(assert-event (equal (len (fn-feed-filename-hex *ff-slash*))
                     (* 2 (len *ff-slash*))))
(assert-event (not (equal (fn-feed-filename-hex '(97 47 98))
                          (fn-feed-filename-hex '(97 95 98)))))
