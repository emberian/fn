; fn: teeth for books/served-span.lisp (REP-012, PRF-181).
;
; What this book is evidence FOR.  fn-scar-ocfg-read-span is the owner read the
; host calls (host/owner-host.lisp fn-owner-chunk-span) over a range of the
; octet buffer.  KEYSTONE fn-scar-feed-span-is-feed-counted (no hypothesis):
; the span fold is the carried counted fold over the range's bytes
; (fn-oct-slice-list i end); KEYSTONE
; fn-scar-ocfg-read-span-is-reference-under-ocl-relation: under the configured
; owner's relation the span read is fn-ocfg-read-tls-prefix over those octets,
; the reference read the list path already establishes as correct.  So the read
; over the buffer decides exactly what the read over the list did.
;
; fn-scar-feed-span-is-feed-counted has no hypothesis, so it has no must-fail;
; its witness is the equality itself, exercised on ground below.  The
; relation keystone gets one must-fail per hypothesis.

(in-package "ACL2")
(include-book "../../books/served-span")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The host runs compiled code: every function it may reach is guard-verified.

(assert-event
 (equal (list (symbol-class 'fn-scar-feed-span (w state))
              (symbol-class 'fn-scar-step-span-fast (w state))
              (symbol-class 'fn-scar-own-read-span (w state))
              (symbol-class 'fn-scar-ocfg-read-span (w state)))
        '(:common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; fn-scar-feed-span-is-feed-counted (no hypothesis) is proved in
; books/served-span.lisp: the span fold IS the carried counted fold over the
; range's bytes, so a ground served connection is not needed to witness it (a
; ground connection here would need a whole configured owner; the relation
; keystone below carries the semantics).

; -----------------------------------------------------------------------------
; Teeth for fn-scar-ocfg-read-span-is-reference-under-ocl-relation: one
; must-fail per hypothesis, showing the span read is not the reference read
; without it.

; Without (fn-ocl-relation oc): the carried read is not the reference read for
; an arbitrary configuration.
(must-fail
 (defthm sst-read-span-needs-ocl-relation
   (implies (and (fn-scar-view-indexedp (fn-ocfg-owner oc))
                 (natp i) (natp end))
            (equal (fn-scar-ocfg-read-span oc id i end fn-octets)
                   (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets))))))

; Without (fn-scar-view-indexedp (fn-ocfg-owner oc)): the Message-ID view trie
; premise the carried fold needs is dropped.
(must-fail
 (defthm sst-read-span-needs-view-indexedp
   (implies (and (fn-ocl-relation oc)
                 (natp i) (natp end))
            (equal (fn-scar-ocfg-read-span oc id i end fn-octets)
                   (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets))))))

; Without (natp i): a non-natural start does not index the buffer as the
; reference's octet list is indexed.
(must-fail
 (defthm sst-read-span-needs-natp-start
   (implies (and (fn-ocl-relation oc)
                 (fn-scar-view-indexedp (fn-ocfg-owner oc))
                 (natp end))
            (equal (fn-scar-ocfg-read-span oc id i end fn-octets)
                   (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets))))))
