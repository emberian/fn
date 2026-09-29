; Teeth for books/frame-buffer.lisp and books/native-control-buffer.lisp:
; the local-control frame decoded and opened in place from the octet buffer
; (D27 row Q2, the frame-control class, PRF-960).
;
; 1. The host's entries are guard-verified with guard T.
; 2. KEYSTONE fn-frb-decode-is-frame-decode and fn-frb-payload-is-window,
;    positive witness: a kind-1 frame with a three-octet payload and an
;    explicit trailer in the live buffer decodes to the reference decode with
;    the payload located (length 3 at offset 10), and the reference's payload
;    is the buffer's window there.  Every error arm agrees: truncated,
;    integrity, limit, length.
; 3. Hypothesis removal for both: a cell that is not an octet (300) in the
;    PAYLOAD.  The antecedent fn-octets-p fails; the reference refuses
;    (:error :malformed) where the twin, which reads the header by index and
;    compares the trailer in place, decodes on, so the conclusions fail.  The
;    digest is explicit: fn-frame-digest is constrained, so a witness that
;    computed it could not be decided.  A corrupted-value witness: no live
;    buffer holds 300.
; 4. KEYSTONE fn-frb-open-with-is-nctrl-open-with (the open with the digest
;    given) and fn-frb-open-payload-with-is-nctrl-open-with: the positive
;    witness in the live buffer for the expected kind and for a wrong kind
;    (both refuse :control-frame); hypothesis removal with the same bad cell.
; 5. fn-frb-open-is-nctrl-open, fn-frb-open-payload-is-nctrl-open and
;    fn-frb-control-decode-is-reference over REAL sealed frames (the window
;    digest through frame-digest-buffer's attachment): a request, a reasoned
;    request (the dispatch's reasoned flag), and a frame of no kind.
; 6. fn-frb-site-decode-is-reference (books/native-live-buffer.lisp): the
;    site's tuple over a live status request (LIVE), a paged report's request
;    (PAGES), and the FNCT request (neither), each equal to the reference's.

(in-package "ACL2")
(include-book "../../books/native-live-buffer")
(include-book "../../books/codec-attach")

(assert-event
 (and (eq (symbol-class 'fn-frb-decode (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-frb-open-with (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-frb-open-payload-with (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-frb-open (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-frb-open-payload (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-frb-control-decode (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-frb-control-reference (w state)) :common-lisp-compliant)
      ; fn-frb-site-decode / -reference: not verifiable while the FNLS
      ; grammars they call are not (books/native-live-buffer.lisp, GUARD DEBT).
      (eq (symbol-class 'fn-frb-nls-open-payload-with (w state)) :common-lisp-compliant)))

; FNCT, version 1, kind 1, length 3 (big-endian u32), then the payload, then
; an explicit 32-octet trailer.
(defconst *frbt-header* '(70 78 67 84 1 1 0 0 0 3))
(defconst *frbt-payload* '(1 2 3))
(defconst *frbt-digest* (make-list 32 :initial-element 7))
(defconst *frbt-frame* (append *frbt-header* *frbt-payload* *frbt-digest*))
(defconst *frbt-bad* (append *frbt-header* '(300 2 3) *frbt-digest*))

; 2. The positive witness, in the live buffer.
(assert-event
 (let* ((fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list *frbt-frame* fn-octets))
        (twin (fn-frb-decode *frbt-digest* *fn-nctrl-max-payload* fn-octets))
        (ref (fn-frame-decode *frbt-frame* *frbt-digest* *fn-nctrl-max-payload*)))
   (mv (and (fn-frame-result-okp twin)
            (fn-frame-result-okp ref)
            (equal twin (fn-frb-of ref))
            (equal (fn-frame-result-payload twin) 3)
            (equal (fn-frame-result-payload ref) *frbt-payload*)
            (equal (fn-frame-result-payload ref)
                   (fn-shr-win *fn-frame-header-octets*
                               (fn-frame-result-payload twin) *frbt-frame*))
            (equal (fn-oct-slice-list 10 13 fn-octets) *frbt-payload*))
       fn-octets))
 :stobjs-out '(nil fn-octets))

; The error arms, each in the live buffer against the reference.
(defun frbt-agreesp (xs digest max-payload fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let* ((fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-octets-append-list xs fn-octets))
         (twin (fn-frb-decode digest max-payload fn-octets))
         (ref (fn-frame-decode xs digest max-payload)))
    (mv (and (equal twin (fn-frb-of ref))
             (not (fn-frame-result-okp ref))
             ref)
        fn-octets)))

(assert-event
 (mv-let (a fn-octets) (frbt-agreesp (butlast *frbt-frame* 1) *frbt-digest* *fn-nctrl-max-payload* fn-octets)
   (mv-let (b fn-octets) (frbt-agreesp *frbt-frame* (make-list 32 :initial-element 8) *fn-nctrl-max-payload* fn-octets)
     (mv-let (c fn-octets) (frbt-agreesp *frbt-frame* *frbt-digest* 2 fn-octets)
       (mv-let (d fn-octets) (frbt-agreesp (append *frbt-frame* '(0)) *frbt-digest* *fn-nctrl-max-payload* fn-octets)
         (mv (and (equal a '(:error :truncated))
                  (equal b '(:error :integrity))
                  (equal c '(:error :limit))
                  (equal d '(:error :length)))
             fn-octets)))))
 :stobjs-out '(nil fn-octets))

; 3. Hypothesis removal, on the logical definitions.
(defthm frbt-decode-hypothesis-removal-witness
  (and (not (fn-octets-p *frbt-bad*))
       (equal (fn-frame-decode *frbt-bad* *frbt-digest* *fn-nctrl-max-payload*)
              '(:error :malformed))
       (fn-frame-result-okp (fn-frb-decode *frbt-digest* *fn-nctrl-max-payload* *frbt-bad*))
       (not (equal (fn-frb-decode *frbt-digest* *fn-nctrl-max-payload* *frbt-bad*)
                   (fn-frb-of (fn-frame-decode *frbt-bad* *frbt-digest*
                                               *fn-nctrl-max-payload*)))))
  :rule-classes nil)

(defthm frbt-window-hypothesis-removal-witness
  (and (not (fn-octets-p *frbt-bad*))
       (not (equal (fn-frame-result-payload
                    (fn-frame-decode *frbt-bad* *frbt-digest* *fn-nctrl-max-payload*))
                   (fn-shr-win *fn-frame-header-octets*
                               (fn-frame-result-payload
                                (fn-frb-decode *frbt-digest* *fn-nctrl-max-payload* *frbt-bad*))
                               *frbt-bad*))))
  :rule-classes nil)

; 4. The open with the digest given, in the live buffer.
(assert-event
 (let* ((fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list *frbt-frame* fn-octets))
        (twin (fn-frb-open-with *frbt-digest* 1 fn-octets))
        (ref (fn-frb-nctrl-open-with *frbt-frame* *frbt-digest* 1)))
   (mv (and (fn-frame-result-okp twin)
            (fn-frame-result-okp ref)
            (equal twin (fn-frb-of ref))
            (equal (fn-frb-open-payload-with *frbt-digest* 1 fn-octets) ref)
            (equal ref (fn-frame-ok *fn-nctrl-magic* 1 1 *frbt-payload*))
            (equal (fn-frb-open-with *frbt-digest* 2 fn-octets) '(:error :control-frame))
            (equal (fn-frb-nctrl-open-with *frbt-frame* *frbt-digest* 2)
                   '(:error :control-frame))
            (equal (fn-frb-open-payload-with *frbt-digest* 2 fn-octets)
                   '(:error :control-frame)))
       fn-octets))
 :stobjs-out '(nil fn-octets))

(defthm frbt-open-with-hypothesis-removal-witness
  (and (not (fn-octets-p *frbt-bad*))
       (equal (fn-frb-nctrl-open-with *frbt-bad* *frbt-digest* 1) '(:error :malformed))
       (fn-frame-result-okp (fn-frb-open-with *frbt-digest* 1 *frbt-bad*))
       (not (equal (fn-frb-open-with *frbt-digest* 1 *frbt-bad*)
                   (fn-frb-of (fn-frb-nctrl-open-with *frbt-bad* *frbt-digest* 1))))
       (not (equal (fn-frb-open-payload-with *frbt-digest* 1 *frbt-bad*)
                   (fn-frb-nctrl-open-with *frbt-bad* *frbt-digest* 1))))
  :rule-classes nil)

; 5. Real frames: the window digest through the attachment.
(defconst *frbt-msgid* (fn-record-string-octets "<control-1@example.invalid>"))
(defconst *frbt-groups* (list (fn-record-string-octets "fn.letters")))
(defconst *frbt-article*
  (fn-record-string-octets
   "From: author@example.invalid\r\nSubject: exact\r\n\r\nbody\r\n"))

(defun frbt-opens-as-reference (frame kind fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let* ((fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-octets-append-list frame fn-octets)))
    (mv (and (equal (fn-frb-open kind fn-octets) (fn-frb-of (fn-nctrl-open frame kind)))
             (equal (fn-frb-open-payload kind fn-octets) (fn-nctrl-open frame kind))
             (equal (fn-frb-control-decode fn-octets) (fn-frb-control-reference frame))
             (fn-frb-control-reference frame))
        fn-octets)))

(assert-event
 (let ((request (fn-native-control-request-encode *frbt-msgid* *frbt-groups* *frbt-article*))
       (reasoned (fn-native-control-reasoned-request-encode
                  *frbt-msgid* *frbt-groups* *frbt-article*)))
   (mv-let (a fn-octets) (frbt-opens-as-reference request *fn-nctrl-request-kind* fn-octets)
     (mv-let (b fn-octets) (frbt-opens-as-reference reasoned *fn-nctrl-reasoned-request-kind* fn-octets)
       (mv-let (c fn-octets) (frbt-opens-as-reference *frbt-frame* *fn-nctrl-request-kind* fn-octets)
         (mv (and (fn-cbor-octet-listp request) (fn-cbor-octet-listp reasoned)
                  ; the plain request: not reasoned, decoded
                  a (equal (first a) nil)
                  (equal (second a) (list :request *frbt-msgid* *frbt-groups* *frbt-article*))
                  ; the reasoned request: the flag, decoded through the reasoned kind
                  b (equal (first b) t)
                  (equal (second b) (list :request *frbt-msgid* *frbt-groups* *frbt-article*))
                  ; a frame whose trailer is not its digest: refused throughout
                  c (equal (first c) nil)
                  (equal (second c) '(:refused :frame)))
             fn-octets)))))
 :stobjs-out '(nil fn-octets))

; 6. The site: FNCT and FNLS from one digest, in the live buffer.
(defun frbt-site-as-reference (frame fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let* ((fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-octets-append-list frame fn-octets)))
    (mv (and (equal (fn-frb-site-decode fn-octets) (fn-frb-site-reference frame))
             (fn-frb-site-reference frame))
        fn-octets)))

(assert-event
 (let ((status (fn-nls-request-encode :status 0))
       (paged (fn-nlp-request-encode :obligations 0 0))
       (request (fn-native-control-request-encode *frbt-msgid* *frbt-groups* *frbt-article*)))
   (mv-let (a fn-octets) (frbt-site-as-reference status fn-octets)
     (mv-let (b fn-octets) (frbt-site-as-reference paged fn-octets)
       (mv-let (c fn-octets) (frbt-site-as-reference request fn-octets)
         (mv (and (fn-cbor-octet-listp status) (fn-cbor-octet-listp paged)
                  ; a live status request: LIVE, not PAGES, no FNCT decode
                  a (equal (len a) 8) (equal (seventh a) t) (equal (eighth a) nil)
                  (equal (second a) '(:refused :frame))
                  ; a paged report's request: PAGES, not LIVE
                  b (equal (seventh b) nil) (equal (eighth b) t)
                  ; the FNCT request: neither, decoded
                  c (equal (seventh c) nil) (equal (eighth c) nil)
                  (equal (second c) (list :request *frbt-msgid* *frbt-groups* *frbt-article*)))
             fn-octets)))))
 :stobjs-out '(nil fn-octets))
