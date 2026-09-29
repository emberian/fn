; native-control-buffer: the local-control frame opened in place from the
; octet buffer (D27, row Q2, the frame-control class; PRF-960).
;
; The reference, `fn-nctrl-open' (books/native-control.lisp), takes the
; frame as an octet list, digests its protected prefix (`fn-frame-trailer'
; of `fn-frame-protected-prefix') and decodes it (`fn-frame-decode');
; every request decoder the host calls (books/native-control.lisp,
; native-control-reason.lisp, consumer-wait-codec.lisp, consumer-reason.lisp,
; topic-history-local-control.lisp) is that open, for its kind, followed by a
; payload grammar over the opened frame.  host/native/control.lisp read one
; frame into a vector and converted it to a list at each of up to nine
; decoder calls per request, each of which digested the whole frame again.
;
; Here the frame is the buffer's value.  The digest is the window digest
; `fn-frame-digest-range' (books/frame-digest-buffer.lisp) of the protected
; prefix, computed ONCE; the decode is `fn-frb-decode' (books/frame-buffer);
; the payload is copied out of its window (one cons of the payload, never of
; the frame) exactly when a grammar needs it as a list.
;
; KEYSTONE fn-frb-open-with-is-nctrl-open-with: with the digest as an
; argument, the buffer open is the reference open, located (`fn-frb-of').
; The digest is an argument so that the keystone's witnesses are decidable
; by evaluation (fn-frame-digest is constrained); fn-frb-open-is-nctrl-open
; composes it with frame-digest-buffer's constraint on the window digest and
; fn-nctrl-open-by-definition.  fn-frb-open-payload-is-nctrl-open: the lift
; to the reference's exact result.  fn-frb-control-decode-is-reference: the
; host site's whole dispatch (which decoders, in which order, with which
; kinds) over the buffer is the same dispatch over the octet list
; (`fn-frb-control-reference'), so ACL2 owns the dispatch and the host only
; destructures it.
;
; The buffer is the control service's own (`fn-octets-ctl', congruent to
; `fn-octets'): the owner's `fn-octets' is filled under the owner's mutex by
; served attempts, and a control client's worker thread decodes before it
; takes that mutex (the fn-octets-bp / fn-octets-pub precedent).

(in-package "ACL2")
(include-book "frame-buffer")
(include-book "frame-digest-buffer")
(include-book "native-control-reason")
(include-book "consumer-reason")
(include-book "topic-history-local-control")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The control service's buffer.

(defabsstobj fn-octets-ctl
  :foundation fn-octets$c
  :recognizer (fn-octets-ctl-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets-ctl :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-octets-ctl-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-ctl-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-ctl-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-ctl-append-octet :logic fn-octets$a-append-octet
                                        :exec fn-octets$c-append-octet :protect t)
            (fn-octets-ctl-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-ctl-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                   :protect t)
            (fn-octets-ctl-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-ctl-from-list :logic fn-octets$a-from-list
                                     :exec fn-octets$c-from-list :protect t)
            (fn-octets-ctl-append-list :logic fn-octets$a-append-list
                                       :exec fn-oct-write-list :protect t)
            (fn-octets-ctl-append-back :logic fn-octets$a-append-back
                                       :exec fn-octets$c-append-back :protect t)
            (fn-octets-ctl-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-octets-ctl-append-word :logic fn-octets$a-append-word
                                       :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

; -----------------------------------------------------------------------------
; The decoded frame's record, read through its lemmas (frame-fields.lisp).

(deftheory fn-frb-frame-record-fns
  '(fn-frame-ok fn-frame-error fn-frame-result-okp fn-frame-result-magic
    fn-frame-result-version fn-frame-result-kind fn-frame-result-payload))

(defthm fn-frb-payload-of-error
  (equal (fn-frame-result-payload (fn-frame-error reason)) nil))

(defthm fn-frb-of-okp
  (equal (fn-frame-result-okp (fn-frb-of r)) (fn-frame-result-okp r))
  :hints (("Goal" :in-theory (e/d (fn-frb-of) (fn-frb-frame-record-fns)))))

; -----------------------------------------------------------------------------
; The reference with its digest as an argument: fn-nctrl-open is this with
; the trailer of the protected prefix.

(defun fn-frb-nctrl-open-with (octets digest expected-kind)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets))
      (fn-frame-error :malformed)
    (let ((opened (fn-frame-decode octets digest *fn-nctrl-max-payload*)))
      (if (and (fn-frame-result-okp opened)
               (equal (fn-frame-result-magic opened) *fn-nctrl-magic*)
               (equal (fn-frame-result-version opened) *fn-nctrl-version*)
               (equal (fn-frame-result-kind opened) expected-kind))
          opened
        (fn-frame-error :control-frame)))))

(defthm fn-nctrl-open-by-definition
  (equal (fn-nctrl-open octets expected-kind)
         (fn-frb-nctrl-open-with octets
                                 (fn-frame-trailer (fn-frame-protected-prefix octets))
                                 expected-kind))
  :hints (("Goal" :in-theory (e/d (fn-nctrl-open) (fn-frame-decode fn-frb-frame-record-fns)))))

; -----------------------------------------------------------------------------
; THE OPEN OVER THE BUFFER, the digest given.

(defun fn-frb-open-with (digest expected-kind fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (let ((opened (fn-frb-decode digest *fn-nctrl-max-payload* fn-octets)))
    (if (and (fn-frame-result-okp opened)
             (equal (fn-frame-result-magic opened) *fn-nctrl-magic*)
             (equal (fn-frame-result-version opened) *fn-nctrl-version*)
             (equal (fn-frame-result-kind opened) expected-kind))
        opened
      (fn-frame-error :control-frame))))

; KEYSTONE.
(defthm fn-frb-open-with-is-nctrl-open-with
  (implies (fn-octets-p fn-octets)
           (equal (fn-frb-open-with digest expected-kind fn-octets)
                  (fn-frb-of (fn-frb-nctrl-open-with fn-octets digest expected-kind))))
  :hints (("Goal" :in-theory (e/d (fn-frb-of fn-oct-octets-p-is-octet-listp)
                                  (fn-frame-decode fn-frb-decode fn-frb-frame-record-fns)))))

; The ok result's payload is a length that fits after the header (the guard
; of the lift below).
(local
 (defthm fn-frb-u32-at-natp
   (implies (and (fn-octets-p fn-octets) (natp j) (<= (+ 4 j) (len fn-octets)))
            (natp (fn-frb-u32-at j fn-octets)))
   :hints (("Goal" :in-theory (enable fn-frb-u32-at fn-oct-octets-p-is-octet-listp)))
   :rule-classes ((:rewrite) (:type-prescription))))

(local
 (defthm fn-frb-open-with-ok-bound
   (implies (and (fn-octets-p fn-octets)
                 (fn-frame-result-okp (fn-frb-open-with digest expected-kind fn-octets)))
            (and (natp (fn-frame-result-payload
                        (fn-frb-open-with digest expected-kind fn-octets)))
                 (<= (+ *fn-frame-header-octets*
                        (fn-frame-result-payload
                         (fn-frb-open-with digest expected-kind fn-octets)))
                     (len fn-octets))))
   :hints (("Goal" :in-theory (e/d (fn-frb-open-with fn-frb-decode)
                                   (fn-frb-decode-is-frame-decode fn-frb-u32-at
                                    fn-frb-magic fn-frb-suffix-equalp
                                    fn-frb-frame-record-fns))))))

; The lift: the reference's exact result, the payload copied out of its
; window (one cons of the payload).
(defun fn-frb-open-payload-with (digest expected-kind fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (let ((opened (fn-frb-open-with digest expected-kind fn-octets)))
    (if (fn-frame-result-okp opened)
        (fn-frame-ok (fn-frame-result-magic opened)
                     (fn-frame-result-version opened)
                     (fn-frame-result-kind opened)
                     (fn-oct-slice-list *fn-frame-header-octets*
                                        (+ *fn-frame-header-octets*
                                           (fn-frame-result-payload opened))
                                        fn-octets))
      opened)))

(verify-guards fn-frb-open-payload-with
  :hints (("Goal" :use fn-frb-open-with-ok-bound
                  :in-theory (disable fn-frb-open-with-is-nctrl-open-with))))

; The reference's payload is the window of its own length after the header
; (fn-frb-payload-is-window, through the open's tests).
(local
 (defthm fn-frb-nctrl-open-with-payload-is-window
   (implies (fn-octets-p fn-octets)
            (equal (fn-frame-result-payload (fn-frb-nctrl-open-with fn-octets digest expected-kind))
                   (fn-shr-win *fn-frame-header-octets*
                               (len (fn-frame-result-payload
                                     (fn-frb-nctrl-open-with fn-octets digest expected-kind)))
                               fn-octets)))
   :hints (("Goal" :use ((:instance fn-frb-payload-is-window
                                    (max-payload *fn-nctrl-max-payload*)))
                   :in-theory (e/d (fn-frb-nctrl-open-with fn-frb-of fn-oct-octets-p-is-octet-listp)
                                   (fn-frame-decode fn-frb-decode fn-frb-frame-record-fns
                                    fn-frb-payload-is-window))))))

(defthm fn-frb-open-payload-with-is-nctrl-open-with
  (implies (fn-octets-p fn-octets)
           (equal (fn-frb-open-payload-with digest expected-kind fn-octets)
                  (fn-frb-nctrl-open-with fn-octets digest expected-kind)))
  :hints (("Goal" :use (fn-frb-open-with-ok-bound fn-frb-nctrl-open-with-payload-is-window)
                  :in-theory (e/d (fn-frb-open-payload-with fn-frb-of fn-oct-octets-p-is-octet-listp
                                   fn-shr-win-is-slice)
                                  (fn-frb-nctrl-open-with fn-frb-frame-record-fns
                                   fn-frb-nctrl-open-with-payload-is-window)))))

; -----------------------------------------------------------------------------
; The digest: the window digest of the protected prefix is the reference's
; trailer of it.

(local
 (defthm fn-frb-octets-true-listp
   (implies (fn-cbor-octet-listp xs) (true-listp xs))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-frb-split-is-take-nthcdr
   (equal (fn-frame-split n xs)
          (if (<= (nfix n) (len xs))
              (cons (take n xs) (nthcdr n xs))
            nil))
   :hints (("Goal" :induct (fn-frame-split n xs)
                   :in-theory (enable (:d fn-frame-split) nthcdr take)))))

(local
 (defthm fn-frb-octet-listp-of-take
   (implies (and (fn-cbor-octet-listp xs) (<= (nfix n) (len xs)))
            (fn-cbor-octet-listp (take n xs)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp take)))))

(local
 (defthm fn-frb-protected-prefix-is-take
   (implies (fn-cbor-octet-listp octets)
            (equal (fn-frame-protected-prefix octets)
                   (take (nfix (- (len octets) *fn-frame-trailer-octets*)) octets)))
   :hints (("Goal" :in-theory (enable fn-frame-protected-prefix)))))

(local
 (defthm fn-frb-reference-digest
   (implies (fn-cbor-octet-listp octets)
            (equal (fn-frame-trailer (fn-frame-protected-prefix octets))
                   (fn-frame-digest (take (nfix (- (len octets) *fn-frame-trailer-octets*))
                                          octets))))))

(local
 (defthm fn-frb-window-digest
   (equal (fn-frame-digest-range nil 0 (nfix (- (len fn-octets) *fn-frame-trailer-octets*))
                                 fn-octets)
          (fn-frame-digest (take (nfix (- (len fn-octets) *fn-frame-trailer-octets*))
                                 fn-octets)))
   :hints (("Goal" :in-theory (enable fn-shr-win)))))

(defun fn-frb-digest (fn-octets)
  ; The trailer the buffer's frame must carry: the window digest of its
  ; protected prefix, computed once per frame.
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-frame-digest-range nil 0
                         (nfix (- (fn-octets-len fn-octets) *fn-frame-trailer-octets*))
                         fn-octets))

(defun fn-frb-open (expected-kind fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-frb-open-with (fn-frb-digest fn-octets) expected-kind fn-octets))

(defun fn-frb-open-payload (expected-kind fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-frb-open-payload-with (fn-frb-digest fn-octets) expected-kind fn-octets))

; fn-nctrl-open's twin, located.
(defthm fn-frb-open-is-nctrl-open
  (implies (fn-octets-p fn-octets)
           (equal (fn-frb-open expected-kind fn-octets)
                  (fn-frb-of (fn-nctrl-open fn-octets expected-kind))))
  :hints (("Goal" :in-theory (e/d (fn-frb-open fn-frb-digest fn-oct-octets-p-is-octet-listp)
                                  (fn-frb-nctrl-open-with fn-frb-of fn-frb-frame-record-fns)))))

; fn-nctrl-open's twin, exactly.
(defthm fn-frb-open-payload-is-nctrl-open
  (implies (fn-octets-p fn-octets)
           (equal (fn-frb-open-payload expected-kind fn-octets)
                  (fn-nctrl-open fn-octets expected-kind)))
  :hints (("Goal" :in-theory (e/d (fn-frb-open-payload fn-frb-digest fn-oct-octets-p-is-octet-listp)
                                  (fn-frb-nctrl-open-with fn-frb-of fn-frb-frame-record-fns)))))

; -----------------------------------------------------------------------------
; THE HOST SITE'S DISPATCH (host/native/control.lisp fnn-control-handle-client):
; which decoders, in which order, with which kinds -- over the octet list
; (the reference) and over the buffer (one digest).

(defun fn-frb-control-reference (octets)
  ; (REASONED REQUEST ADMIN MODERATION TOPIC CONSUMER): the reasoned flag
  ; (host/native-control-host.lisp fn-native-control-host-reasoned-framep),
  ; the request and admin decodes of the reasoned kinds when it holds and of
  ; the plain kinds otherwise, the moderation request, the topic request,
  ; and the consumer request (the plain decode, else the reasoned one).
  (declare (xargs :guard t))
  (let* ((reasoned (or (fn-native-control-reasoned-framep octets)
                       (fn-ncr-framep octets)))
         (request (if reasoned
                      (fn-native-control-reasoned-request-decode octets)
                    (fn-native-control-request-decode octets)))
         (admin (if reasoned
                    (fn-native-control-reasoned-admin-decode octets)
                  (fn-native-control-admin-decode octets)))
         (moderation (fn-native-control-moderation-decode octets))
         (topic (fn-thlc-request-decode octets))
         (plain (fn-cwait-request-decode octets))
         (consumer (if (and (consp plain) (eq (car plain) :consumer))
                       plain
                     (fn-ncr-request-decode octets))))
    (list reasoned request admin moderation topic consumer)))

(defun fn-frb-control-decode (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (let* ((digest (fn-frb-digest fn-octets))
         (reasoned (or (fn-frame-result-okp
                        (fn-frb-open-with digest *fn-nctrl-reasoned-request-kind* fn-octets))
                       (fn-frame-result-okp
                        (fn-frb-open-with digest *fn-nctrl-reasoned-admin-kind* fn-octets))
                       (fn-frame-result-okp
                        (fn-frb-open-with digest *fn-nctrl-moderation-request-kind* fn-octets))
                       (fn-frame-result-okp
                        (fn-frb-open-with digest *fn-ncr-request-kind* fn-octets))))
         (request (fn-nctrl-request-payload-decode
                   (fn-frb-open-payload-with digest
                                             (if reasoned
                                                 *fn-nctrl-reasoned-request-kind*
                                               *fn-nctrl-request-kind*)
                                             fn-octets)))
         (admin (fn-nctrl-admin-payload-decode
                 (fn-frb-open-payload-with digest
                                           (if reasoned
                                               *fn-nctrl-reasoned-admin-kind*
                                             *fn-nctrl-admin-kind*)
                                           fn-octets)))
         (moderation (fn-nctrl-moderation-payload-decode
                      (fn-frb-open-payload-with digest *fn-nctrl-moderation-request-kind*
                                                fn-octets)))
         (topic (fn-thlc-request-payload-decode
                 (fn-frb-open-payload-with digest *fn-thlc-request-kind* fn-octets)))
         (plain (fn-cwait-request-payload-decode
                 (fn-frb-open-payload-with digest *fn-ncl-request-kind* fn-octets)))
         (consumer (if (and (consp plain) (eq (car plain) :consumer))
                       plain
                     (fn-ncr-request-payload-decode
                      (fn-frb-open-payload-with digest *fn-ncr-request-kind* fn-octets)))))
    (list reasoned request admin moderation topic consumer)))

(defthm fn-frb-control-decode-is-reference
  (implies (fn-octets-p fn-octets)
           (equal (fn-frb-control-decode fn-octets)
                  (fn-frb-control-reference fn-octets)))
  :hints (("Goal" :in-theory (e/d (fn-frb-control-decode fn-frb-control-reference fn-frb-digest
                                   fn-oct-octets-p-is-octet-listp
                                   fn-native-control-reasoned-framep fn-ncr-framep
                                   fn-native-control-reasoned-request-decode
                                   fn-native-control-request-decode
                                   fn-native-control-reasoned-admin-decode
                                   fn-native-control-admin-decode
                                   fn-native-control-moderation-decode
                                   fn-thlc-request-decode fn-cwait-request-decode
                                   fn-ncr-request-decode)
                                  (fn-frb-nctrl-open-with fn-frb-of fn-frb-frame-record-fns
                                   fn-nctrl-request-payload-decode fn-nctrl-admin-payload-decode
                                   fn-nctrl-moderation-payload-decode
                                   fn-thlc-request-payload-decode
                                   fn-cwait-request-payload-decode
                                   fn-ncr-request-payload-decode)))))
