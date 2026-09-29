; native-live-buffer: the whole local-control site decoded in place from the
; control buffer, FNCT and FNLS, from one digest (D27, row Q2, the
; frame-control and status classes; PRF-960).
;
; host/native/control.lisp fnn-control-handle-client decides, over one read
; frame, the FNCT decoders (books/native-control-buffer.lisp
; `fn-frb-control-decode', the dispatch tuple) and then whether the frame is
; a live status request (host/native-live-status-host.lisp
; fn-native-live-status-host-requestp: `fn-cev-any-request-decode' answers
; :live-status) or a paged report's request
; (fn-native-live-pages-host-requestp: `fn-nlp-request-decode' answers
; :page).  The FNLS frame is the FNCT frame's layout with FNLS's magic,
; version, payload bound and refusal (`fn-nls-open', books/native-live-status),
; so its open is the family open with those constants
; (fn-nls-open-by-definition, fn-frb-nls-open-payload-with), and the frame's
; digest -- the trailer of its protected prefix -- is the same digest for
; both families: `fn-frb-site-decode' computes it once.
;
; fn-frb-site-decode-is-reference: the site's tuple over the buffer is
; `fn-frb-site-reference' of the octet list: the FNCT dispatch's six, then
; LIVE and PAGES as the host decided them.  ACL2 owns the whole site's
; dispatch; the host destructures it.

(in-package "ACL2")
(include-book "native-control-buffer")
(include-book "control-evidence")
(include-book "native-live-pages")

; -----------------------------------------------------------------------------
; FNLS's instance of the family.

(defun fn-frb-nls-open-with (octets digest expected-kind)
  (declare (xargs :guard t))
  (fn-frb-ref-open-as octets *fn-nls-magic* *fn-nls-version* *fn-nls-max-payload*
                      :live-status-frame digest expected-kind))

(defthm fn-nls-open-by-definition
  (equal (fn-nls-open octets expected-kind)
         (fn-frb-nls-open-with octets
                               (fn-frame-trailer (fn-frame-protected-prefix octets))
                               expected-kind))
  :hints (("Goal" :in-theory (e/d (fn-nls-open fn-frb-nls-open-with fn-frb-ref-open-as)
                                  (fn-frame-decode fn-frb-frame-record-fns)))))

(defun fn-frb-nls-open-payload-with (digest expected-kind fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-frb-open-payload-as *fn-nls-magic* *fn-nls-version* *fn-nls-max-payload*
                          :live-status-frame digest expected-kind fn-octets))

(defthm fn-frb-nls-open-payload-with-is-nls-open-with
  (implies (fn-octets-p fn-octets)
           (equal (fn-frb-nls-open-payload-with digest expected-kind fn-octets)
                  (fn-frb-nls-open-with fn-octets digest expected-kind)))
  :hints (("Goal" :in-theory (e/d (fn-frb-nls-open-payload-with fn-frb-nls-open-with)
                                  (fn-frb-open-payload-as fn-frb-ref-open-as
                                   fn-frb-frame-record-fns)))))

; -----------------------------------------------------------------------------
; THE SITE.

(defun fn-frb-site-reference (octets)
  ; The FNCT dispatch's (REASONED REQUEST ADMIN MODERATION TOPIC CONSUMER),
  ; then LIVE (fn-native-live-status-host-requestp) and PAGES
  ; (fn-native-live-pages-host-requestp, asked only when not LIVE).
  (declare (xargs :guard t :verify-guards nil))
  (let* ((live (equal (car (fn-cev-any-request-decode octets)) :live-status))
         (pages (and (not live)
                     (equal (car (fn-nlp-request-decode octets)) :page))))
    (append (fn-frb-control-reference octets) (list live pages))))

(defun fn-frb-site-decode (fn-octets)
  (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
  (let* ((digest (fn-frb-digest fn-octets))
         (control (fn-frb-control-decode-with digest fn-octets))
         (plain (fn-nls-request-payload-decode
                 (fn-frb-nls-open-payload-with digest *fn-nls-request-kind* fn-octets)))
         (any (if (equal (car plain) :live-status)
                  plain
                (fn-cev-request-payload-decode
                 (fn-frb-nls-open-payload-with digest *fn-cev-request-kind* fn-octets))))
         (live (equal (car any) :live-status))
         (pages (and (not live)
                     (equal (car (fn-nlp-request-payload-decode
                                  (fn-frb-nls-open-payload-with digest *fn-nlp-request-kind*
                                                                fn-octets)))
                            :page))))
    (append control (list live pages))))

(defthm fn-frb-site-decode-is-reference
  (implies (fn-octets-p fn-octets)
           (equal (fn-frb-site-decode fn-octets)
                  (fn-frb-site-reference fn-octets)))
  :hints (("Goal" :use fn-frb-control-decode-is-reference
                  :in-theory (e/d (fn-frb-site-decode fn-frb-site-reference fn-frb-control-decode
                                   fn-oct-octets-p-is-octet-listp
                                   fn-cev-any-request-decode fn-nls-request-decode
                                   fn-cev-request-decode fn-nlp-request-decode)
                                  (fn-frb-digest fn-frb-nls-open-with fn-frb-ref-open-as
                                   fn-frb-nls-open-payload-with fn-frb-open-payload-as
                                   fn-frb-of fn-frb-frame-record-fns
                                   fn-frb-control-decode-with fn-frb-control-reference
                                   fn-frb-control-decode-is-reference
                                   fn-nls-request-payload-decode fn-cev-request-payload-decode
                                   fn-nlp-request-payload-decode)))))

; GUARD DEBT, by name (pre-existing, not this book's): fn-nls-request-decode,
; fn-cev-request-decode, fn-nlp-request-decode and fn-cev-any-request-decode
; (books/native-live-status, control-evidence, native-live-pages) were
; admitted with :verify-guards nil and never verified -- their record reads
; (fn-record-read-uint) need the payload as an octet list, which an ok frame
; always is (fn-frame-decode-payload-octets) but their grammars do not
; state.  Their -payload-decode halves inherit it, and so do
; fn-frb-site-reference and fn-frb-site-decode here (the FNCT half,
; fn-frb-control-decode-with, is verified).  The site entry therefore runs
; the FNLS grammars as the host ran them before: through the executable
; counterparts.  Verifying them is a change to those books' grammars (an
; octet-list test on the payload, or the lemma), owed by the status class.
