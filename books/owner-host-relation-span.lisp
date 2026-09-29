; owner-host-relation-span.lisp -- the relation the host carries across the
; served read (fn-ohr-, lane owner-relation-2, row Q3c).
;
; host/owner-host.lisp fn-owner-chunk-span-at reads a span of the connection's
; buffer through five layers, each a named refinement of the one below when
; its own condition holds (the refused arms -- no credit, the slots exceeded,
; the disk shedding, a capture held -- are that layer's own reads and are
; not this theorem's subject):
;   fn-mca-read-span   books/owner-credits.lisp          within the credit: fn-oas-read-span
;   fn-oas-read-span   books/owner-article-slots.lisp    within the slots:  fn-otm-read-span
;   fn-otm-read-span   books/owner-time-admission.lisp   admitted:          fn-orr-read-span
;   fn-orr-read-span   books/owner-reader-read.lisp      no capture:        fn-scr-ocfg-read-span
;   fn-scr-ocfg-read-span  books/served-catalog-chain.lisp  under the relation, the view index and
;                      the catalog: fn-ocfg-read-tls-prefix of the octet slice, which is fn-ocfg-read
;                      of the consumed prefix (books/owner-tls-prefix.lisp), which keeps the relation
;                      (books/config-owner-live-read.lisp fn-ocl-read-preserves-historical-relation).
; A separate book because the base relation book's closure stops at the
; carried read (fn-scar-ocfg-read-tls-prefix, fn-ohr-chunk-preserves-ocl-relation).

(in-package "ACL2")

(include-book "owner-host-relation")
(include-book "owner-credits")

(local (in-theory (disable fn-mca-read-span fn-oas-read-span fn-otm-read-span fn-orr-read-span
                           fn-scr-ocfg-read-span fn-ocfg-read-tls-prefix fn-ocfg-read
                           fn-ocl-relation fn-oas-over-p fn-otm-admit-post fn-mcr-resize
                           fn-mca-need fn-mca-conn-key fn-own-tls-result-owner
                           fn-own-tls-result-consumed fn-oct-slice-list)))

; KEYSTONE for the host line: within the credit, within the slots, admitted,
; with no capture held, under the relation, the view index and the catalog,
; the served read of the span keeps the configured owner's relation.
(defthm fn-ohr-read-span-preserves-ocl-relation
  (implies (and (fn-ocl-relation oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                (fn-scol-okp fn-arena fn-cat)
                (natp i) (natp end)
                (fn-wire-statep (fn-own-conn-wire (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                (not (consp views))
                (not (eq (fn-otm-admit-post s) :shed))
                (not (fn-oas-over-p oc (fn-own-tls-result-owner
                                        (fn-otm-read-span oc views id i end s fn-octets fn-arena fn-cat))
                                    id slots))
                (equal (car (fn-mcr-resize credits (fn-mca-conn-key id)
                                           (fn-mca-need (fn-own-tls-result-owner
                                                         (fn-oas-read-span oc views id i end s slots
                                                                           fn-octets fn-arena fn-cat))
                                                        id reserve)))
                       :ok))
           (fn-ocl-relation
            (fn-own-tls-result-owner
             (car (fn-mca-read-span credits oc views id i end s slots reserve fn-octets fn-arena fn-cat)))))
  :hints (("Goal"
           :use (fn-mca-read-span-within-the-credit-unfolds
                 fn-oas-read-span-when-held-unfolds
                 fn-otm-read-span-when-admitted-unfolds
                 fn-orr-read-span-without-a-capture-is-the-span-read-by-definition
                 fn-scr-ocfg-read-span-is-reference-under-ocl-relation
                 (:instance fn-ocfg-read-tls-prefix-is-read-of-consumed-prefix
                            (octets (fn-oct-slice-list i end fn-octets)))
                 (:instance fn-ocl-read-preserves-historical-relation
                            (octets (take (fn-own-tls-result-consumed
                                           (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena))
                                          (fn-oct-slice-list i end fn-octets)))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-ohr-read-span-preserves-carried-relation
  (implies (and (fn-lgoc-invariantp oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                (fn-scol-okp fn-arena fn-cat)
                (natp i) (natp end)
                (fn-wire-statep (fn-own-conn-wire (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                (not (consp views))
                (not (eq (fn-otm-admit-post s) :shed))
                (not (fn-oas-over-p oc (fn-own-tls-result-owner
                                        (fn-otm-read-span oc views id i end s fn-octets fn-arena fn-cat))
                                    id slots))
                (equal (car (fn-mcr-resize credits (fn-mca-conn-key id)
                                           (fn-mca-need (fn-own-tls-result-owner
                                                         (fn-oas-read-span oc views id i end s slots
                                                                           fn-octets fn-arena fn-cat))
                                                        id reserve)))
                       :ok))
           (fn-lgoc-invariantp
            (fn-own-tls-result-owner
             (car (fn-mca-read-span credits oc views id i end s slots reserve fn-octets fn-arena fn-cat)))))
  :hints (("Goal"
           :use (fn-ohr-read-span-preserves-ocl-relation
                 fn-mca-read-span-within-the-credit-unfolds
                 fn-oas-read-span-when-held-unfolds
                 fn-otm-read-span-when-admitted-unfolds
                 fn-orr-read-span-without-a-capture-is-the-span-read-by-definition
                 fn-scr-ocfg-read-span-is-reference-under-ocl-relation
                 (:instance fn-ocfg-read-tls-prefix-is-read-of-consumed-prefix
                            (octets (fn-oct-slice-list i end fn-octets)))
                 (:instance fn-ohr-carried-of-same-store
                            (x (cdr (fn-ocfg-read oc id
                                                  (take (fn-own-tls-result-consumed
                                                         (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena))
                                                        (fn-oct-slice-list i end fn-octets))
                                                  fn-arena))))
                 (:instance fn-ocl-own-read-keeps-store
                            (o (fn-ocfg-owner oc))
                            (octets (take (fn-own-tls-result-consumed
                                           (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena))
                                          (fn-oct-slice-list i end fn-octets))))
                 (:instance fn-ocl-ocfg-read-unfolds
                            (octets (take (fn-own-tls-result-consumed
                                           (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena))
                                          (fn-oct-slice-list i end fn-octets)))))
           :in-theory (union-theories '(fn-ohr-carried-implies-ocl-relation fn-ohr-with-owner-store
                                        fn-ocfg-with-read-owner)
                                      (theory 'minimal-theory)))))
