; Layer C's served run assembly (C-ONE-ASSEMBLY): the production schemas
; (identity, article metadata, overview, addressing) assembled once, with
; the identity decision. A world holds one assembly; the node's assembly
; (assembly-index through machines-c) and every C unit include this book.
; The range reads are assembled on top of it in range-served.lisp, so each
; book stays under the minute.
(in-package "ACL2")
(include-book "identity")
(include-book "ordered")
(fn2-book-layer :c)
(fn2-run-assemble)
(fn2-identity-assemble)
