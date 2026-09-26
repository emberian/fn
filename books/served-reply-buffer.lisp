; fn: a served step's reply as a range of the octet buffer (D27; PRF-192;
; PKT-491, the reply-side twin of ingress-span's span read).
;
; A served step answers with EFFECTS; the reply the host writes is
; `fn-served-reply-octets' of them (books/served.lisp): every `(:reply
; octets)' effect's octets, in order.  Until this book the owner built that
; reply as one octet list (`fn-owner-install-effects' puts it in
; `fn-owner-output'), the host re-walked it to check it was octets, and then
; coerced the list into a byte vector for the socket: a 3 MiB ARTICLE made a
; 48 MiB cons list and walked it three times.
;
; `fn-served-reply-to-buffer' writes the same octets into the octet buffer
; `fn-octets' (books/octets-stobj.lisp: a byte array whose logical value is
; the octet list): the buffer is cleared and each reply effect's octets are
; appended by ONE `fn-octets-append-list' export call, one array write per
; octet and no cons.  The host then writes the buffer's range [0, len) to
; the socket (host/native/owner.lisp fnn-owner-handle-chunk, through
; host/owner-host.lisp fn-owner-reply-buffer).
;
; The boundary theorem (keystone) `fn-served-reply-to-buffer-is-the-reply':
; the answer OKP is exactly "every reply effect carries an octet list", and
; when it holds the buffer's range [0, len), read by `fn-oct-slice-list',
; is `fn-served-reply-octets' of the effects, so the bytes the host writes
; from the range are the reply the served machine decided.  When OKP is
; false the buffer is unchanged and the host faults (as it faulted on a
; non-octet `fn-owner-output' before).
;
; What does not move: the effects (and so the exposure's observation,
; `fn-exp-observe-effects', which already reads the effects and not the
; reply) and every served decision; this book only changes where the reply's
; octets are put.

(in-package "ACL2")
(include-book "served")
(include-book "octets-stobj")

; The octets one effect contributes to the reply: exactly the term
; `fn-served-reply-octets' appends.
(defun fn-srb-effect-octets (e)
  (declare (xargs :guard t))
  (if (and (consp e) (equal (car e) :reply) (consp (cdr e)))
      (car (cdr e))
    nil))

; Every reply effect carries an octet list.  Checked once per step, with no
; allocation; it is the check the host made on the list before
; (fnn-owner-octets-global), now made by ACL2 per effect.
(defun fn-srb-effects-octetsp (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (and (fn-cbor-octet-listp (fn-srb-effect-octets (car effects)))
           (fn-srb-effects-octetsp (cdr effects)))
    t))

(defun fn-srb-append-effects (effects fn-octets)
  (declare (xargs :stobjs fn-octets :guard (fn-srb-effects-octetsp effects)))
  (if (consp effects)
      (let ((fn-octets (fn-octets-append-list (fn-srb-effect-octets (car effects))
                                              fn-octets)))
        (fn-srb-append-effects (cdr effects) fn-octets))
    fn-octets))

; The host-called subject: (mv okp fn-octets).
(defun fn-served-reply-to-buffer (effects fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (fn-srb-effects-octetsp effects)
      (let* ((fn-octets (fn-octets-clear fn-octets))
             (fn-octets (fn-srb-append-effects effects fn-octets)))
        (mv t fn-octets))
    (mv nil fn-octets)))

; -----------------------------------------------------------------------------
; The list facts.

(local
 (defthm fn-srb-served-reply-octets-step
   (equal (fn-served-reply-octets (cons e effects))
          (append (fn-srb-effect-octets e) (fn-served-reply-octets effects)))
   :hints (("Goal" :in-theory (enable fn-served-reply-octets)))))

(local
 (defthm fn-srb-append-assoc
   (equal (append (append x y) z) (append x (append y z)))))

(local
 (defthm fn-srb-octet-listp-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))
   :rule-classes :forward-chaining))

(local
 (defthm fn-srb-append-effects-is-append-of-the-reply
   ; Appending the effects' octets is appending the reply, over any true
   ; list (the buffer's value always is one: its recognizer).
   (implies (and (true-listp fn-octets) (fn-srb-effects-octetsp effects))
            (equal (fn-srb-append-effects effects fn-octets)
                   (append fn-octets (fn-served-reply-octets effects))))
   :hints (("Goal" :induct (fn-srb-append-effects effects fn-octets)
                   :in-theory (enable fn-oct-append-list-is-append)))))

(local
 (defthm fn-srb-effects-octetsp-reply-is-octet-list
   (implies (fn-srb-effects-octetsp effects)
            (fn-cbor-octet-listp (fn-served-reply-octets effects)))
   :hints (("Goal" :induct (fn-srb-effects-octetsp effects)))))

(local
 (defthm fn-srb-take-of-len
   (implies (true-listp x) (equal (take (len x) x) x))))

; -----------------------------------------------------------------------------
; The boundary theorem.

(defthm fn-served-reply-to-buffer-is-the-reply
  ; KEYSTONE (PRF-192).  The subject is what host/owner-host.lisp
  ; fn-owner-reply-buffer calls for every served read
  ; (host/native/owner.lisp fnn-owner-handle-chunk).  OKP is exactly the
  ; octet check; when it holds, the buffer's length is the reply's and its
  ; range [0, len) is the reply octets, which is what the host writes.
  (let* ((r (fn-served-reply-to-buffer effects fn-octets))
         (okp (mv-nth 0 r))
         (buf (mv-nth 1 r)))
    (and (equal okp (fn-srb-effects-octetsp effects))
         (implies okp
                  (and (equal (fn-octets-len buf)
                              (len (fn-served-reply-octets effects)))
                       (equal (fn-oct-slice-list 0 (fn-octets-len buf) buf)
                              (fn-served-reply-octets effects))))))
  :hints (("Goal" :in-theory (enable fn-oct-len-is-len))))

(defthm fn-served-reply-to-buffer-refusal-keeps-the-buffer
  ; A step whose effects carry a non-octet reply leaves the buffer as it
  ; was; the host faults on OKP = nil and writes nothing from the range.
  (implies (not (fn-srb-effects-octetsp effects))
           (equal (mv-nth 1 (fn-served-reply-to-buffer effects fn-octets))
                  fn-octets)))

(in-theory (disable fn-served-reply-to-buffer))
