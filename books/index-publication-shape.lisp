; Exact immutable publication record, factored without changing field order
; or accessor/constructor bodies. Shape alone is not publication authority.
(in-package "ACL2")
(include-book "acceptance-alloc")
(include-book "defrecord")

(fn-defrecord fn-ipub
  :tag :index-publication
  :constructor (fn-ipub-make generation key pages count frontier view
                            table-root table-depth table-id row-root row-depth row-id
                            number-root number-id completion visibility-source arena-incarnation arena-prefix)
  :fields ((fn-ipub-generation t) (fn-ipub-key t) (fn-ipub-pages t)
           (fn-ipub-count t) (fn-ipub-frontier t) (fn-ipub-view t)
           (fn-ipub-table-root t) (fn-ipub-table-depth t) (fn-ipub-table-id t)
           (fn-ipub-row-root t) (fn-ipub-row-depth t) (fn-ipub-row-id t)
           (fn-ipub-number-root t) (fn-ipub-number-id t) (fn-ipub-completion t)
           (fn-ipub-visibility-source t) (fn-ipub-arena-incarnation t) (fn-ipub-arena-prefix t))
  :recognizer nil)
