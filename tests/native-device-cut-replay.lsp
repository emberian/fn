; Read-only consumer of one selected native run and its complete image copies.
(in-package "ACL2")
(set-ld-error-action '(:exit 2) state)
(include-book "sim/native-device-cut" :uncertified-okp nil)
:q
(load "tests/native-device-cut-raw.lsp")
(sb-ext:exit :code 0)
