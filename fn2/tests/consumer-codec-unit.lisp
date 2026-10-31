; The consumer port's frames against fn1's bytes (fn2/books/consumer-codec.lisp;
; e-surface.md 3.1, 4.2). The cursor fixtures are fn1's own vectors, read from
; tests/fixtures/consumer-position/; the request payloads are fn1's encoders'
; octets (books/consumer-local-control.lisp fn-ncl-request-encode,
; consumer-wait-codec.lisp fn-cwait-request-encode) written out by hand from
; their definitions; the trailer is BLAKE3-256, checked at a known answer.
; Every fixture is also run through the generated (served) codec.
(in-package "ACL2")
(include-book "../books/consumer-codec")
(include-book "layout-unit")
(include-book "std/io/read-file-bytes" :dir :system)

(defmacro fn2-cct-fixture (name file)
  `(make-event
    (mv-let (bytes state) (read-file-bytes ,file state)
      (if (stringp bytes) (er soft 'fn2-cct-fixture "~s0" bytes)
        (value (list 'defconst ',name (list 'quote bytes)))))))
(fn2-cct-fixture *fn2-cct-five-field* "../../tests/fixtures/consumer-position/five-field-v1.fncu")
(fn2-cct-fixture *fn2-cct-max-cursor* "../../tests/fixtures/consumer-position/max-cursor-v1.fncu")
(fn2-cct-fixture *fn2-cct-zero-position* "../../tests/fixtures/consumer-position/zero-position-high-octets-v1.fncu")

;; 1. fn1's cursors decode, carry fn1's fields, and re-encode to fn1's octets.
(defconst *fn2-cct-ff* (make-list 64 :initial-element 255))
(assert-event
 (and (equal (fn2-fncu-decode *fn2-cct-five-field*)
             '(:ok (:cursor 0 (1) (2) (3) (4) (5) 1 1 1 5)))
      (equal (fn2-fncu-decode *fn2-cct-max-cursor*)
             (list :ok (list :cursor 0 *fn2-cct-ff* *fn2-cct-ff* *fn2-cct-ff* *fn2-cct-ff* *fn2-cct-ff*
                             4294967295 4294967295 4294967295 4294967295)))
      (equal (fn2-fncu-decode *fn2-cct-zero-position*)
             (list :ok (list :cursor 0 *fn2-cct-ff* *fn2-cct-ff* *fn2-cct-ff* *fn2-cct-ff* *fn2-cct-ff* 1 1 1 0)))
      (equal (len *fn2-cct-max-cursor*) 346)
      (equal (fn2-fncu-encode (cadr (fn2-fncu-decode *fn2-cct-five-field*))) *fn2-cct-five-field*)
      (equal (fn2-fncu-encode (cadr (fn2-fncu-decode *fn2-cct-max-cursor*))) *fn2-cct-max-cursor*)
      (equal (fn2-fncu-encode (cadr (fn2-fncu-decode *fn2-cct-zero-position*))) *fn2-cct-zero-position*)))

;; 2. Past a v1 field the cursor is v2, never truncated; one form per cursor.
(defconst *fn2-cct-wide* '(:cursor 0 (1) (2) (3) (4) (5) 1 1 1 4294967296))
(defconst *fn2-cct-domain* '(:cursor 7 (1) (2) (3) (4) (5) 1 1 1 5))
(assert-event
 (and (equal (nth 4 (fn2-fncu-encode *fn2-cct-wide*)) 2)
      (equal (len (fn2-fncu-encode *fn2-cct-wide*)) (+ 5 10 4 32))
      (equal (fn2-fncu-decode (fn2-fncu-encode *fn2-cct-wide*)) (list :ok *fn2-cct-wide*))
      (equal (fn2-fncu-decode (fn2-fncu-encode *fn2-cct-domain*)) (list :ok *fn2-cct-domain*))
      (equal (fn2-layout-max-size *fn2-fncu-v2-layout*) 366)
      ; a v2 form of a cursor that fits v1
      (equal (fn2-fncu-decode (fn2-layout-octets *fn2-fncu-v2-layout*
                                (list *fn2-fncu-magic* 2 '(1) '(2) '(3) '(4) '(5) 0 1 1 1 5)))
             '(:refused :grammar))))

;; 3. fn1's cursor refusals, word for word.
(assert-event
 (and (equal (fn2-fncu-decode (make-list 513 :initial-element 0)) '(:refused :octets))
      (equal (fn2-fncu-decode (update-nth 4 3 *fn2-cct-five-field*)) '(:refused :version))
      (equal (fn2-fncu-decode (update-nth 0 70 *fn2-cct-five-field*)) '(:refused :version))
      (equal (fn2-fncu-decode (butlast *fn2-cct-five-field* 1)) '(:refused :grammar))
      (equal (fn2-fncu-decode (append *fn2-cct-five-field* '(0))) '(:refused :grammar))
      ; a zero registration epoch, and an empty ID
      (equal (fn2-fncu-decode (update-nth 26 0 *fn2-cct-five-field*)) '(:refused :grammar))
      (equal (fn2-fncu-decode (append (take 5 *fn2-cct-five-field*) '(0) (nthcdr 7 *fn2-cct-five-field*)))
             '(:refused :grammar))))

;; 4. The frame: BLAKE3-256 at a known answer, then seal and open.
(assert-event
 (equal (fn-blake3 nil)
        '(#xaf #x13 #x49 #xb9 #xf5 #xf9 #xa1 #xa6 #xa0 #x40 #x4d #xea #x36 #xdc #xc9 #x49
          #x9b #xcb #x25 #xc9 #xad #xc1 #x12 #xb7 #xcc #x9a #x93 #xca #xe4 #x1f #x32 #x62)))
(defconst *fn2-cct-mini* '(109 105 110 105))
(defconst *fn2-cct-pass* '(112 97 115 115))
(defconst *fn2-cct-register* (list* 0 4 (append *fn2-cct-mini* '(2 103 49))))
(defconst *fn2-cct-frame* (fn2-fnct-seal 4 *fn2-cct-register*))
(assert-event
 (and (equal (take 10 *fn2-cct-frame*) '(70 78 67 84 1 4 0 0 0 9))
      (equal (len *fn2-cct-frame*) (+ 10 9 32))
      (equal (fn2-fnct-open *fn2-cct-frame* 513) (list :ok 4 *fn2-cct-register*))
      (equal (fn2-fnct-open (update-nth 50 (logxor 1 (nth 50 *fn2-cct-frame*)) *fn2-cct-frame*) 513)
             '(:refused :frame))
      (equal (fn2-fnct-open (update-nth 12 7 *fn2-cct-frame*) 513) '(:refused :frame))
      (equal (fn2-fnct-open (append *fn2-cct-frame* '(0)) 513) '(:refused :frame))
      (equal (fn2-fnct-open (butlast *fn2-cct-frame* 1) 513) '(:refused :frame))
      (equal (fn2-fnct-open (update-nth 0 71 *fn2-cct-frame*) 513) '(:refused :frame))
      (equal (fn2-fnct-open *fn2-cct-frame* 8) '(:refused :size))))

;; 5. fn1's kind 4 payloads, codes 0-10: each decodes to its word and fields
;; and re-encodes to the same octets.
(defconst *fn2-cct-legacy*
  `((:register ,*fn2-cct-register*)
    (:ack (1 ,@*fn2-cct-five-field*))
    (:position (2 4 ,@*fn2-cct-mini*))
    (:unregister (3 4 ,@*fn2-cct-mini*))
    (:bootstrap (4))
    (:poll (5 4 ,@*fn2-cct-mini*))
    (:status (6 4 ,@*fn2-cct-mini*))
    (:bound-poll (7 4 ,@*fn2-cct-mini* 0 4 ,@*fn2-cct-pass*))
    (:bound-ack (8 0 4 ,@*fn2-cct-pass* ,@*fn2-cct-five-field*))
    (:wait (9 4 ,@*fn2-cct-mini* 0 0 0 30))
    (:bound-wait (10 4 ,@*fn2-cct-mini* 0 0 0 30 0 4 ,@*fn2-cct-pass*))))
; The port's own payloads (codes 11-18), from fields.
(defconst *fn2-cct-port*
  `((:append ((stream . (103 49)) (op . (111 112 49)) (article . (65 66 67))))
    (:rebase ((cursor . ,*fn2-cct-five-field*) (streams . (2 103 49 2 103 50)) (start . 0)))
    (:fetch ((message-id . (60 97 64 98 62)) (domain . 0) (position . 4294967300)))
    (:register-query ((consumer . ,*fn2-cct-mini*) (streams . (2 103 49)) (start . 1)))
    (:read ((cursor . ,*fn2-cct-five-field*) (max-items . 16) (max-octets . 65536)))
    (:wait-cursor ((cursor . ,*fn2-cct-five-field*) (max-items . 16) (max-octets . 65536) (seconds . 30)))
    (:unregister-cursor ((cursor . ,*fn2-cct-five-field*)))
    (:status-wide ((consumer . ,*fn2-cct-mini*)))))
(defun fn2-cct-legacy-ok (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (b* (((list word payload) (car rows))
         (r (fn2-fnct-request-decode payload)))
      (and (eq (car r) :request) (eq (cadr r) word)
           (equal (fn2-fnct-request-encode word (caddr r)) payload)
           (fn2-cct-legacy-ok (cdr rows))))))
(defun fn2-cct-port-ok (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (b* (((list word alist) (car rows))
         (payload (fn2-fnct-request-encode word alist))
         (r (fn2-fnct-request-decode payload)))
      (and (consp payload) (equal r (list :request word alist))
           (fn2-cct-port-ok (cdr rows))))))
(assert-event (and (fn2-cct-legacy-ok *fn2-cct-legacy*) (fn2-cct-port-ok *fn2-cct-port*)
                   (equal (len *fn2-cct-legacy*) 11)))

;; 6. fn1's request refusals, word for word (the field that failed; trailing
;; octets are the last field's).
(defconst *fn2-cct-refusals*
  `(((0 0 2 103 49) :consumer)
    ((0 4 ,@*fn2-cct-mini*) :group)
    ((0 4 ,@*fn2-cct-mini* 2 103 49 7) :group)
    ((0 65 ,@(make-list 65 :initial-element 1) 2 103 49) :consumer)
    ((2 4 ,@*fn2-cct-mini* 7) :consumer)
    ((2) :consumer)
    ((4 0) :bootstrap)
    ((99) :kind)
    ((1 ,@(butlast *fn2-cct-five-field* 1)) :cursor)
    ((7 4 ,@*fn2-cct-mini* 0 0) :secret)
    ((7 4 ,@*fn2-cct-mini* 1 241 ,@(make-list 497 :initial-element 1)) :secret)
    ((8 0 4 ,@*fn2-cct-pass* 9) :cursor)
    ((9 4 ,@*fn2-cct-mini* 0 0 14 17) :timeout)
    ((9 4 ,@*fn2-cct-mini* 0 0 0) :timeout)
    ((9 4 ,@*fn2-cct-mini* 0 0 0 30 1) :timeout)
    ((10 4 ,@*fn2-cct-mini* 0 0 0 30) :secret)
    ((2 ,@(make-list 513 :initial-element 1)) :size)
    ((7 ,@(make-list 1024 :initial-element 1)) :size)
    ((99 ,@(make-list 513 :initial-element 1)) :size)
    ((15 0 3 1 2 3 0 0 0 1 0 0 0 1) :cursor)
    ((11 0 0 0 0 0 0 0 0) :stream)))
(defun fn2-cct-refusals-ok (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (and (equal (fn2-fnct-request-decode (caar rows)) (list :refused (cadar rows)))
         (fn2-cct-refusals-ok (cdr rows)))))
(assert-event (fn2-cct-refusals-ok *fn2-cct-refusals*))

;; 7. Replies: fn1's kinds 5, 6 and 9, and the port's kind 28.
(assert-event
 (and (equal (fn2-fnct-reply :accepted *fn2-cct-five-field*) (cons 0 *fn2-cct-five-field*))
      (equal (fn2-fnct-reply :refused nil) '(1))
      (equal (fn2-fnct-reply :uncertain nil) '(2))
      (equal (fn2-fnct-status-reply :accepted 7 9) '(0 0 0 0 7 0 0 0 9 0 0 0 2))
      (equal (fn2-fnct-status-reply :refused nil nil) '(1))
      (equal (fn2-fnct-poll-reply :accepted '(9 9) nil) '(0 0 0 0 2 9 9 0 0 0 0))
      (equal (fn2-fnct-poll-reply :refused nil nil) '(1 0 0 0 0 0 0 0 0))
      (equal (fn2-layout-octets *fn2-fnct-port-reply-layout* '(1 (98 101 104 105 110 100) nil))
             '(1 0 6 98 101 104 105 110 100 0 0 0 0))))

;; 8. The served codec: every fixture payload through the generated decoder
;; and encoder of its code's layout agrees with the list specification.
(make-event
 (value `(progn ,@(fn2-layout-test-dispatch-events
                  'fn2-cct-codec (table-alist 'fn2-layouts (w state))
                  '(:encode :decode)))))
(defun fn2-cct-layout (payload)
  (declare (xargs :verify-guards nil))
  (b* ((row (assoc (car payload) *fn2-fnct-codes*)))
    (cons '(code :u8) (caddr row))))
(defun fn2-cct-served-layout (layout payload tail fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
  (b* (((mv mc values rest) (fn2-layout-parse layout payload))
       (fn2-pool (fn2-layout-test-write payload 0 0 fn2-pool))
       ((mv code next fn2-fields) (fn2-cct-codec-decode layout 0 0 1 0 (len payload) 1 0 1 fn2-fields fn2-pool))
       ((unless (and (eq mc :ok) (eq code :ok) (equal next (- (len payload) (len rest)))
                     (or tail (null rest))
                     (equal values (fn2-layout-test-values layout 0 fn2-fields fn2-pool))))
        (mv (list :served-decode (take 2 payload) mc code) fn2-fields fn2-pool))
       ((mv fn2-fields fn2-pool) (fn2-layout-test-put layout values 0 0 fn2-fields fn2-pool))
       ((mv ec end fn2-pool) (fn2-cct-codec-encode layout 0 1 1 0 1 0 1 fn2-fields fn2-pool)))
    (mv (if (and (eq ec :ok) (equal (fn2-layout-test-read end 1 0 fn2-pool) (take next payload))) t
          (list :served-encode (take 2 payload) ec))
        fn2-fields fn2-pool)))
(defun fn2-cct-served-all (payloads fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
  (if (atom payloads) (mv t fn2-fields fn2-pool)
    (b* ((payload (car payloads))
         ((mv ok fn2-fields fn2-pool)
          (fn2-cct-served-layout (fn2-cct-layout payload) payload
                                 (cadddr (assoc (car payload) *fn2-fnct-codes*)) fn2-fields fn2-pool)))
      (if (eq ok t) (fn2-cct-served-all (cdr payloads) fn2-fields fn2-pool) (mv ok fn2-fields fn2-pool)))))
(defun fn2-cct-served-all-cursors (cursors fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
  (if (atom cursors) (mv t fn2-fields fn2-pool)
    (b* (((mv ok fn2-fields fn2-pool)
          (fn2-cct-served-layout *fn2-fncu-v1-layout* (car cursors) nil fn2-fields fn2-pool)))
      (if (eq ok t) (fn2-cct-served-all-cursors (cdr cursors) fn2-fields fn2-pool) (mv ok fn2-fields fn2-pool)))))
(defun fn2-cct-port-payloads (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (cons (fn2-fnct-request-encode (caar rows) (cadar rows)) (fn2-cct-port-payloads (cdr rows)))))
(defun fn2-cct-served ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-fields
    (mv-let (ok fn2-fields)
      (with-local-stobj fn2-pool
        (mv-let (ok fn2-fields fn2-pool)
          (b* (((mv fn2-fields fn2-pool) (fn2-layout-test-init fn2-fields fn2-pool))
               ((mv ok fn2-fields fn2-pool)
                (fn2-cct-served-all (append (strip-cadrs *fn2-cct-legacy*) (fn2-cct-port-payloads *fn2-cct-port*))
                                    fn2-fields fn2-pool))
               ((unless (eq ok t)) (mv ok fn2-fields fn2-pool))
               ; fn1's three cursors through the generated v1 codec
               ((mv ok fn2-fields fn2-pool)
                (fn2-cct-served-all-cursors (list *fn2-cct-five-field* *fn2-cct-max-cursor* *fn2-cct-zero-position*)
                                            fn2-fields fn2-pool))
               ((unless (eq ok t)) (mv ok fn2-fields fn2-pool))
               ; the check has teeth: a truncated cursor is a disagreement, not a pass
               ((mv bad fn2-fields fn2-pool) (fn2-cct-served-layout *fn2-fncu-v1-layout* (butlast *fn2-cct-five-field* 1) nil fn2-fields fn2-pool)))
            (mv (if (eq bad t) :no-teeth t) fn2-fields fn2-pool))
          (mv ok fn2-fields)))
      ok)))
(assert-event (equal (fn2-cct-served) t))
