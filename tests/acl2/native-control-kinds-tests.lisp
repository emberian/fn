; Teeth for books/native-control-kinds.lisp (sweep S029).
;
; 1. The host's entry is guard-verified with guard T.
; 2. KEYSTONE fn-ctlk-every-handled-frame-is-classified (no hypotheses),
;    positive witnesses: real frames the chain's decoders accept -- the TLS
;    reload and status requests, the login-bindings reload, a keys redecide
;    and a hybrid revocation -- each decoded and classified with its
;    handler's word, over the list and in the live control buffer.
; 3. Mutation witnesses (labelled): an operator post frame, which no handler
;    decodes, is classified nil, so the chain is never asked about it; a
;    store-kind frame with one payload octet flipped still classifies :store
;    while its decoder refuses it (the word is a superset of what decodes,
;    never a subset); a frame whose magic is not FNCT classifies nil.

(in-package "ACL2")
(include-book "../../books/native-control-kinds")

(assert-event
 (eq (symbol-class 'fn-ctlk-frame-handler (w state)) :common-lisp-compliant))

(defconst *ckt-reload* (fn-tlsr-request-encode :reload))
(defconst *ckt-status* (fn-tlsr-request-encode :status))
(defconst *ckt-bindings* (fn-pinv-bindings-request-encode))
(defconst *ckt-redecide* (fn-pinv-redecide-request-encode
                          (fn-record-string-octets "<m@x>")))
(defconst *ckt-revoke* (fn-native-hybrid-control-revoke-encode
                        1 (make-list 32 :initial-element 7)))
(defconst *ckt-post* (fn-native-control-request-encode
                      (fn-record-string-octets "<p@x>")
                      (list (fn-record-string-octets "fn.test"))
                      (fn-record-string-octets "Subject: s")))

; The word for XS, from the live control buffer filled with XS.
(defun ckt-word (xs fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let* ((fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-octets-append-list xs fn-octets)))
    (mv (fn-ctlk-frame-handler fn-octets) fn-octets)))

(defmacro ckt-is (xs word)
  `(assert-event (mv-let (w fn-octets) (ckt-word ,xs fn-octets)
                   (mv (equal w ,word) fn-octets))
                 :stobjs-out '(nil fn-octets)))

; 2. Each frame decodes and is classified with its handler's word.
(ckt-is *ckt-reload* :read)
(ckt-is *ckt-status* :read)
(ckt-is *ckt-bindings* :store)
(ckt-is *ckt-redecide* :store)
(ckt-is *ckt-revoke* :store)
(assert-event
 (and (fn-cbor-octet-listp *ckt-reload*)
      (equal (fn-tlsr-request-decode *ckt-reload*) :reload)
      (equal (fn-tlsr-request-decode *ckt-status*) :status)
      (fn-pinv-bindings-request-decode *ckt-bindings*)
      (equal (fn-pinv-redecide-request-decode *ckt-redecide*)
             (fn-record-string-octets "<m@x>"))
      (fn-native-hybrid-control-revoke-decode *ckt-revoke*)))

; The same in the live control buffer (the stobj the host fills).
(assert-event
 (let* ((fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list *ckt-redecide* fn-octets))
        (a (equal (fn-ctlk-frame-handler fn-octets) :store))
        (fn-octets (fn-octets-clear fn-octets))
        (fn-octets (fn-octets-append-list *ckt-post* fn-octets))
        (b (null (fn-ctlk-frame-handler fn-octets))))
   (mv (and a b) fn-octets))
 :stobjs-out '(nil fn-octets))

; 3. Mutation witnesses.
; (a) An operator post: no handler decodes it, and it is classified nil.
(assert-event
 (and (consp *ckt-post*)
      (null (fn-tlsr-request-decode *ckt-post*))
      (null (fn-pinv-bindings-request-decode *ckt-post*))
      (null (fn-pinv-redecide-request-decode *ckt-post*))
      (null (fn-native-hybrid-control-author-decode *ckt-post*))))
(ckt-is *ckt-post* nil)
; (b) A redecide frame with its last payload octet flipped: the decoder
; refuses it (integrity), the word stays :store.
(defconst *ckt-flipped*
  (let ((n (- (len *ckt-redecide*) 33)))
    (append (take n *ckt-redecide*)
            (list (logxor 1 (nth n *ckt-redecide*)))
            (nthcdr (+ n 1) *ckt-redecide*))))
(assert-event (null (fn-pinv-redecide-request-decode *ckt-flipped*)))
(ckt-is *ckt-flipped* :store)
; (c) Not FNCT magic: nil.
(ckt-is (cons 0 (cdr *ckt-redecide*)) nil)
