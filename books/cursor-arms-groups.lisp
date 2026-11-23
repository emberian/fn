(in-package "ACL2")
(include-book "cursor-arms-seek")
(fn2-book-layer :d)
; Both classifier outcomes meet the arm's resource bound. Keep the command
; dispatch closed in its generated quantity proof.
(local (table fn2-arms-quantity-opaque 'fn2-cursor-sub-seek-identity-children
              '(fn2-cursor-hdr-p fn2-cursor-overview-p)))
(fn2-arms-child-shard fn2-cursor fn2-cursor-sub-seek-selected
  fn2-cursor-sub-end-list)
