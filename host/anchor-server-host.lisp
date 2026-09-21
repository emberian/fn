; fn: program-mode bridge for the ACL2-owned pinned anchor server manifest.

(in-package "ACL2")
(include-book "../books/anchor-servers")

(set-state-ok t)
(program)

(defun fn-anchor-server-host-find (name-octets)
  (fn-anchor-server-find name-octets))

(defun fn-anchor-server-host-select (name-octets timeout-seconds)
  (fn-anchor-server-select name-octets timeout-seconds))

(logic)
