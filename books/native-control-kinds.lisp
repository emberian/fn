; fn: which local-control frames the handler chain answers, read from the
; frame's header in place (sweep S029, 2026-10-03).
;
; host/native/control.lisp fnn-control-handle-client asks the handler chain
; (host/native tls-reload, login-bindings, keys, peer-invite and
; hybrid-control: *fnn-hybrid-control-handler*) about a frame before its own
; arms.  Each handler turned the whole frame into an octet list and ran its
; decoders over it, for EVERY frame -- an operator post of an article at the
; profile's bound five times over -- and the chain ran before the disk-stall
; shed (PRF-311), so its mutating requests were never answered BUSY.
;
; Here the frame's FNCT kind is read from its header in the control buffer
; (no digest, no list), and `fn-ctlk-frame-handler' answers :store for a
; kind whose handler writes the Store or the configuration (the hybrid
; enrolment, author and revocation requests, peer issue, accept and confirm,
; keys redecide, the login-bindings reload), :read for the TLS request
; (reload or status: a handshake context, no Store write), and nil for
; every other frame.  The host asks the chain only on a non-nil word and
; sheds a :store word like every other mutating request.
;
; KEYSTONE fn-ctlk-every-handled-frame-is-classified: every frame any of the
; chain's decoders accepts is classified with its handler's word, so asking
; the chain only on a non-nil word drops no request it would have answered.
; No hypothesis: each decoder refuses anything that is not an FNCT frame of
; its own kind.
;
; This book owns the prefix `fn-ctlk-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "native-control-buffer")
(include-book "frame-buffer")
(include-book "tls-reload")
(include-book "peer-invite")
(include-book "native-hybrid-control")

; -----------------------------------------------------------------------------
; The kinds.

(defconst *fn-ctlk-store-kinds*
  (list *fn-nhctrl-enroll-kind* *fn-nhctrl-author-kind* *fn-nhctrl-revoke-kind*
        *fn-nhctrl-enroll-next-kind* *fn-nhctrl-revoke-next-kind*
        *fn-pinv-issue-kind* *fn-pinv-accept-kind* *fn-pinv-confirm-kind*
        *fn-pinv-redecide-kind* *fn-pinv-bindings-kind*))

(defconst *fn-ctlk-read-kinds* (list *fn-tlsr-request-kind*))

(defun fn-ctlk-word (kind)
  (declare (xargs :guard t))
  (cond ((member-equal kind *fn-ctlk-store-kinds*) :store)
        ((member-equal kind *fn-ctlk-read-kinds*) :read)
        (t nil)))

; The FNCT header's kind octet (offset 5, after the four magic octets and the
; version), or nil when the buffer holds no FNCT header.
(defun fn-ctlk-header-kind (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (and (<= *fn-frame-header-octets* (fn-octets-len fn-octets))
           (equal (fn-frb-magic fn-octets) *fn-nctrl-magic*)
           (equal (fn-octets-get 4 fn-octets) *fn-nctrl-version*))
      (fn-octets-get 5 fn-octets)
    nil))

; THE FUNCTION THE HOST CALLS (through host/native-control-host.lisp
; fn-native-control-host-frame-handler, from host/native/control.lisp
; fnn-control-handle-client).
(defun fn-ctlk-frame-handler (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-ctlk-word (fn-ctlk-header-kind fn-octets)))

; -----------------------------------------------------------------------------
; An opened frame's kind is its header's.

(local
 (defthm fn-ctlk-frb-decode-ok-reads-the-header
   (implies (fn-frame-result-okp (fn-frb-decode digest max-payload fn-octets))
            (and (<= *fn-frame-header-octets* (fn-octets-len fn-octets))
                 (equal (fn-frame-result-magic (fn-frb-decode digest max-payload fn-octets))
                        (fn-frb-magic fn-octets))
                 (equal (fn-frame-result-version (fn-frb-decode digest max-payload fn-octets))
                        (fn-octets-get 4 fn-octets))
                 (equal (fn-frame-result-kind (fn-frb-decode digest max-payload fn-octets))
                        (fn-octets-get 5 fn-octets))))
   :hints (("Goal" :in-theory (e/d (fn-frb-decode)
                                   (fn-frb-magic fn-frb-u32-at
                                    fn-frb-suffix-equalp))))))

(local
 (defthm fn-ctlk-frb-of-keeps-the-head
   (and (equal (fn-frame-result-okp (fn-frb-of r)) (fn-frame-result-okp r))
        (implies (fn-frame-result-okp r)
                 (and (equal (fn-frame-result-magic (fn-frb-of r))
                             (fn-frame-result-magic r))
                      (equal (fn-frame-result-version (fn-frb-of r))
                             (fn-frame-result-version r))
                      (equal (fn-frame-result-kind (fn-frb-of r))
                             (fn-frame-result-kind r)))))
   :hints (("Goal" :in-theory (enable fn-frb-of)))))

(defthm fn-ctlk-opened-fnct-kind-is-the-header-kind
  (implies (and (fn-cbor-octet-listp octets)
                (fn-frame-result-okp (fn-frame-decode octets digest max-payload))
                (equal (fn-frame-result-magic (fn-frame-decode octets digest max-payload))
                       *fn-nctrl-magic*)
                (equal (fn-frame-result-version (fn-frame-decode octets digest max-payload))
                       *fn-nctrl-version*))
           (equal (fn-ctlk-header-kind octets)
                  (fn-frame-result-kind (fn-frame-decode octets digest max-payload))))
  :hints (("Goal" :use ((:instance fn-frb-decode-is-frame-decode (fn-octets octets))
                        (:instance fn-ctlk-frb-decode-ok-reads-the-header
                                   (fn-octets octets)))
                  :in-theory (e/d (fn-oct-octets-p-is-octet-listp)
                                  (fn-frb-decode-is-frame-decode
                                   fn-ctlk-frb-decode-ok-reads-the-header
                                   fn-frb-decode fn-frame-decode fn-frb-of
                                   fn-frb-magic)))))

; -----------------------------------------------------------------------------
; The opens the chain's decoders use, each FNCT of its own kind.

(local
 (defthm fn-ctlk-nctrl-open-kind
   (implies (fn-frame-result-okp (fn-nctrl-open octets kind))
            (equal (fn-ctlk-header-kind octets) kind))
   :hints (("Goal" :in-theory (e/d (fn-nctrl-open) (fn-frame-decode
                                                   fn-ctlk-header-kind))))))

(local
 (defthm fn-ctlk-nhctrl-open-values-kind
   (implies (fn-nhctrl-open-values octets kind specs)
            (equal (fn-ctlk-header-kind octets) kind))
   :hints (("Goal" :in-theory (e/d (fn-nhctrl-open-values)
                                   (fn-frame-decode fn-ctlk-header-kind
                                    fn-frame-fields-parse))))))

; KEYSTONE.  No hypothesis.
(defthm fn-ctlk-every-handled-frame-is-classified
  (and (implies (fn-tlsr-request-decode octets)
                (equal (fn-ctlk-frame-handler octets) :read))
       (implies (fn-pinv-bindings-request-decode octets)
                (equal (fn-ctlk-frame-handler octets) :store))
       (implies (fn-pinv-redecide-request-decode octets)
                (equal (fn-ctlk-frame-handler octets) :store))
       (implies (fn-pinv-request-decode kind octets)
                (equal (fn-ctlk-frame-handler octets) :store))
       (implies (fn-pinv-confirm-request-decode octets)
                (equal (fn-ctlk-frame-handler octets) :store))
       (implies (fn-native-hybrid-control-enroll-decode octets)
                (equal (fn-ctlk-frame-handler octets) :store))
       (implies (fn-native-hybrid-control-author-decode octets)
                (equal (fn-ctlk-frame-handler octets) :store))
       (implies (fn-native-hybrid-control-revoke-decode octets)
                (equal (fn-ctlk-frame-handler octets) :store))
       (implies (fn-native-hybrid-control-enroll-next-decode octets)
                (equal (fn-ctlk-frame-handler octets) :store))
       (implies (fn-native-hybrid-control-revoke-next-decode octets)
                (equal (fn-ctlk-frame-handler octets) :store)))
  :hints (("Goal" :use ((:instance fn-ctlk-nctrl-open-kind (kind *fn-tlsr-request-kind*))
                        (:instance fn-ctlk-nhctrl-open-values-kind (kind *fn-pinv-bindings-kind*) (specs *fn-pinv-request-spec*))
                        (:instance fn-ctlk-nhctrl-open-values-kind (kind *fn-pinv-redecide-kind*) (specs *fn-pinv-request-spec*))
                        (:instance fn-ctlk-nhctrl-open-values-kind (kind *fn-pinv-issue-kind*) (specs *fn-pinv-request-spec*))
                        (:instance fn-ctlk-nhctrl-open-values-kind (kind *fn-pinv-accept-kind*) (specs *fn-pinv-request-spec*))
                        (:instance fn-ctlk-nhctrl-open-values-kind (kind *fn-pinv-confirm-kind*) (specs *fn-pinv-confirm-request-spec*))
                        (:instance fn-ctlk-nhctrl-open-values-kind (kind *fn-nhctrl-enroll-kind*) (specs *fn-nhctrl-enroll-spec*))
                        (:instance fn-ctlk-nhctrl-open-values-kind (kind *fn-nhctrl-author-kind*) (specs *fn-nhctrl-author-spec*))
                        (:instance fn-ctlk-nhctrl-open-values-kind (kind *fn-nhctrl-revoke-kind*) (specs *fn-nhctrl-revoke-spec*))
                        (:instance fn-ctlk-nhctrl-open-values-kind (kind *fn-nhctrl-enroll-next-kind*) (specs *fn-nhctrl-enroll-next-spec*))
                        (:instance fn-ctlk-nhctrl-open-values-kind (kind *fn-nhctrl-revoke-next-kind*) (specs *fn-nhctrl-revoke-next-spec*)))
                  :in-theory (e/d (fn-tlsr-request-decode
                                   fn-pinv-bindings-request-decode
                                   fn-pinv-redecide-request-decode
                                   fn-pinv-request-decode fn-pinv-request-kindp
                                   fn-pinv-confirm-request-decode
                                   fn-native-hybrid-control-enroll-decode
                                   fn-native-hybrid-control-author-decode
                                   fn-native-hybrid-control-revoke-decode
                                   fn-native-hybrid-control-enroll-next-decode
                                   fn-native-hybrid-control-revoke-next-decode)
                                  (fn-nctrl-open fn-nhctrl-open-values
                                   fn-ctlk-header-kind fn-frame-fields-parse
                                   fn-ctlk-nctrl-open-kind
                                   fn-ctlk-nhctrl-open-values-kind)))))
