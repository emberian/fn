; fn: the standalone Store's POST prepare decides the served groups itself
; (lane prepare-served, 2026-09-27; PKT-827 (d)).  Before this book
; host/store-node-host.lisp fn-store-sn-prepare tested
; fn-cnode-selection-servedp in host code, then called
; fn-store-prepare-carried-next, which stages a record whatever its groups.
;
; This book shares the prefix `fn-psrv-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "store-prepare-carried")
(include-book "store-number-bound")

; RFC 3977 section 6's number test over the wire record's groups at the
; Store's node (books/store-number-bound.lisp fn-snb-groups-fitp; PKT-615).
(defun fn-psrv-store-numberedp (s w)
  (declare (xargs :guard t))
  (fn-snb-groups-fitp (fn-record-groups w)
                      (fn-state-nexts (fn-node-acceptance (fn-sn-node s)))))

; THE STANDALONE STORE'S PREPARE (host/store-node-host.lisp
; fn-store-sn-prepare; host/native/io.lisp fnn-bridge-prepare): the wire
; record W is staged by fn-store-prepare-carried-next only when the live
; configuration CONFIG serves its groups and their numbers stay within RFC
; 3977 section 6's bound.
(defun fn-psrv-store-prepare-next (config s w count)
  (declare (xargs :guard (and (fn-sn-statep s) (natp count))))
  (if (and (fn-record-p w)
           (fn-cnode-selection-servedp config (fn-record-groups w))
           (fn-psrv-store-numberedp s w))
      (fn-store-prepare-carried-next s w count)
    s))

; Its word when it left the Store unchanged: :article-numbers-exhausted for a
; served record whose numbers would pass the bound, else :refused.
(defun fn-psrv-store-refusal-kind (config s w)
  (declare (xargs :guard t))
  (if (and (fn-record-p w)
           (fn-cnode-selection-servedp config (fn-record-groups w))
           (not (fn-psrv-store-numberedp s w)))
      :article-numbers-exhausted
    :refused))

(defthm fn-psrv-store-prepare-next-cases
  (equal (fn-psrv-store-prepare-next config s w count)
         (if (and (fn-cnode-selection-servedp config (fn-record-groups w))
                  (fn-psrv-store-numberedp s w))
             (fn-store-prepare-carried-next s w count)
           s))
  :hints (("Goal" :in-theory (enable fn-store-prepare-carried-next))))

; A served record past the bound leaves the Store unchanged and is named.
(defthm fn-psrv-store-prepare-refuses-exhausted
  (implies (and (fn-record-p w)
                (fn-cnode-selection-servedp config (fn-record-groups w))
                (not (fn-psrv-store-numberedp s w)))
           (and (equal (fn-psrv-store-prepare-next config s w count) s)
                (equal (fn-psrv-store-refusal-kind config s w)
                       :article-numbers-exhausted))))

(in-theory (disable fn-psrv-store-prepare-next fn-psrv-store-numberedp
                    fn-psrv-store-refusal-kind))
