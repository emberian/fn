; Compression declares policy fields on the shared concrete codec envelope.
(in-package "ACL2")
(include-book "codec-transport")
(fn2-book-layer :a)
(defcodec-transport fn2-compress-transport
 ((input-quantum :u32) (output-quantum :u32)
  (credit :u32) (ratio :u32) (burst :u32))
 :rows-bound 2)
