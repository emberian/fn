; Independent big-endian fixtures for the bounded raw export surface.
; These are transport fixtures: a resume's entry semantics and published-cut
; binding belong to the served decision, not this structural codec.
(in-package "ACL2")
(include-book "../books/consumer-codec")
(include-book "layout-unit")

(defconst *fn2-pect-start* '(19 0 0 0 0 0 0 0 0 0 0 0 7))
(defconst *fn2-pect-request-layout*
  '((code :u8) (cut :u64be) (resume (:octets16 400)) (max-items :u16be)))
; CUT = 0x0102030405060708, opaque resume octets, MAX-ITEMS = 0x0102.
(defconst *fn2-pect-resume* '(19 1 2 3 4 5 6 7 8 0 3 9 10 11 1 2))
; Empty scan-end, with coverage explicitly limited to local observations.
(defconst *fn2-pect-empty* '(1 1 0 1 2 3 4 5 6 7 8 0 0 0 0 0 0 0))
; Page-bound, NEXT = (9 10 11); one length-framed opaque entry (20 21).
(defconst *fn2-pect-page*
  '(1 1 0 0 0 0 0 0 0 0 9 1 0 3 9 10 11 0 1 0 4 0 2 20 21))
(assert-event
 (and (equal (fn2-fnct-request-decode *fn2-pect-start*)
             '(:request :evidence-page ((cut . 0) (resume) (max-items . 7))))
      (equal (fn2-fnct-request-decode *fn2-pect-resume*)
             '(:request :evidence-page ((cut . 72623859790382856)
                                       (resume 9 10 11) (max-items . 258))))
      (equal (fn2-fnct-request-encode :evidence-page
                '((cut . 72623859790382856) (resume 9 10 11) (max-items . 258)))
             *fn2-pect-resume*)
      (equal (fn2-fnct-max-payload 19) 413)
      (equal (fn2-layout-max-size *fn2-peer-export-result-layout*) 4514)
      (equal (fn2-layout-octets *fn2-peer-export-length-layout* '(258)) '(1 2))
      (equal (fn2-layout-octets *fn2-peer-export-result-layout*
                               '(1 1 0 72623859790382856 0 nil 0 nil))
             *fn2-pect-empty*)
      (equal (fn2-layout-octets *fn2-peer-export-result-layout*
                               '(1 1 0 9 1 (9 10 11) 1 (0 2 20 21)))
             *fn2-pect-page*)))

; Exactly 400 resume octets are structurally valid. 401 is refused, including
; a short buffer whose declared length alone exceeds the cap.
(defconst *fn2-pect-cap*
  (append '(19 0 0 0 0 0 0 0 9 1 144)
          (make-list 400 :initial-element 17) '(0 1)))
(assert-event
 (and (equal (fn2-fnct-request-decode *fn2-pect-cap*)
             (list :request :evidence-page
                   (list '(cut . 9) (cons 'resume (make-list 400 :initial-element 17))
                         '(max-items . 1))))
      (equal (fn2-fnct-request-decode
               (append '(19 0 0 0 0 0 0 0 9 1 145)
                       (make-list 401 :initial-element 17) '(0 1)))
             '(:refused :size))
      (equal (fn2-fnct-request-decode '(19 0 0 0 0 0 0 0 9 1 145))
             '(:refused :grammar))
      (equal (fn2-fnct-request-decode (butlast *fn2-pect-resume* 1))
             '(:refused :grammar))
      (equal (fn2-fnct-request-decode (append *fn2-pect-start* '(0)))
             '(:refused :grammar))))

; Exercise generated concrete codecs against handwritten expected values.
(make-event
 (value `(progn ,@(fn2-layout-test-dispatch-events
                   'fn2-pect-codec (table-alist 'fn2-layouts (w state))
                   '(:encode :decode)))))
(defun fn2-pect-served-one (layout bytes expected fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
  (b* ((fn2-pool (fn2-layout-test-write bytes 0 0 fn2-pool))
       ((mv code next fn2-fields)
        (fn2-pect-codec-decode layout 0 0 1 0 (len bytes) 1 0 1 fn2-fields fn2-pool))
       ((unless expected) (mv (not (eq code :ok)) fn2-fields fn2-pool))
       ((unless (and (eq code :ok) (equal next (len bytes))
                     (equal (fn2-layout-test-values layout 0 fn2-fields fn2-pool) expected)))
        (mv nil fn2-fields fn2-pool))
       ((mv fn2-fields fn2-pool) (fn2-layout-test-put layout expected 0 0 fn2-fields fn2-pool))
       ((mv ec end fn2-pool)
        (fn2-pect-codec-encode layout 0 1 1 0 1 0 1 fn2-fields fn2-pool)))
    (mv (and (eq ec :ok) (equal end (len bytes))
             (equal (fn2-layout-test-read end 1 0 fn2-pool) bytes)) fn2-fields fn2-pool)))
(defun fn2-pect-served-rows (rows fn2-fields fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
  (if (atom rows) (mv t fn2-fields fn2-pool)
    (b* (((list layout bytes expected) (car rows))
         ((mv ok fn2-fields fn2-pool)
          (fn2-pect-served-one layout bytes expected fn2-fields fn2-pool)))
      (if ok (fn2-pect-served-rows (cdr rows) fn2-fields fn2-pool)
        (mv nil fn2-fields fn2-pool)))))
(defun fn2-pect-served ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-fields
    (mv-let (ok fn2-fields)
      (with-local-stobj fn2-pool
        (mv-let (ok fn2-fields fn2-pool)
          (b* (((mv fn2-fields fn2-pool) (fn2-layout-test-init fn2-fields fn2-pool)))
            (fn2-pect-served-rows
             (list
              (list *fn2-pect-request-layout* *fn2-pect-start* '(19 0 nil 7))
              (list *fn2-pect-request-layout* *fn2-pect-resume*
                    '(19 72623859790382856 (9 10 11) 258))
              (list *fn2-pect-request-layout* *fn2-pect-cap*
                    (list 19 9 (make-list 400 :initial-element 17) 1))
              (list *fn2-pect-request-layout* (butlast *fn2-pect-resume* 1) nil)
              (list *fn2-pect-request-layout* '(19 0 0 0 0 0 0 0 9 1 145) nil)
              (list *fn2-peer-export-result-layout* *fn2-pect-empty*
                    '(1 1 0 72623859790382856 0 nil 0 nil))
              (list *fn2-peer-export-result-layout* *fn2-pect-page*
                    '(1 1 0 9 1 (9 10 11) 1 (0 2 20 21)))
              (list *fn2-peer-export-result-layout* (butlast *fn2-pect-page* 1) nil)
              ; NEXT length 401 and ENTRIES length 4097 exceed their caps.
              (list *fn2-peer-export-result-layout*
                    '(1 1 0 0 0 0 0 0 0 0 9 1 1 145) nil)
              (list *fn2-peer-export-result-layout*
                    '(1 1 0 0 0 0 0 0 0 0 9 0 0 0 0 0 16 1) nil)
              (list *fn2-peer-export-length-layout* '(1 2) '(258)))
             fn2-fields fn2-pool))
          (mv ok fn2-fields)))
      ok)))
(assert-event (fn2-pect-served))
