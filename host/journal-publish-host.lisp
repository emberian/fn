; Program bridge for the immutable journal publication phase machine.
(in-package "ACL2")
(include-book "../books/journal-publish")
(include-book "../books/app-journal")
(include-book "../books/definterface")

(include-book "../books/entries-journal-publish-host")

(definterface fn-jpub-host-step
  :class ::ideal)

(definterface fn-jpub-host-action
  :class ::ideal)

(definterface fn-jpub-host-phase
  :class ::ideal)

(definterface fn-jpub-host-outcome
  :class ::ideal)
(defun fn-jpub-host-terminalp (publication)
  (if (fn-jpub-terminalp publication) t nil))

(definterface fn-jpub-host-terminalp
  :class ::ideal)
(defun fn-jpub-host-authorized-initialp (publication)
  (if (equal publication (fn-jpub-initial t)) t nil))

(definterface fn-jpub-host-authorized-initialp
  :class ::ideal)

; Native application journals carry this value from their one bounded recovery
; scan.  Each append asks ACL2 to authorize the exact next immutable name and
; its successor frontier; raw Lisp never recomputes capacity or sequence.

(definterface fn-aj-host-initial
  :class ::ideal
  :keystones ((fn-aj-statep-of-initial :via fn-aj-initial)
              (fn-aj-valid-profile-admits-first-work :via fn-aj-initial)))
; The journal's profile (D27, lane caps): the file's name and read bound, its
; reading (NIL refuses the open) and the octets a write publishes for the
; journal whose frontier is FRONTIER (NIL refuses the write).

(definterface fn-aj-host-profile-file-name
  :class ::ideal)

(definterface fn-aj-host-profile-read-bound
  :class ::ideal)

(definterface fn-aj-host-profile-read
  :class ::ideal
  :keystones ((fn-ajpf-read-of-octets :via fn-ajpf-read)
              (fn-ajpf-read-is-a-profile :via fn-ajpf-read)))

(definterface fn-aj-host-profile-write-octets
  :class ::ideal
  :exempt ((octets "the profile's max-octets bound, a natural the operator gave, not bytes"))
  :keystones ((fn-ajpf-write-keeps-the-journal :via fn-ajpf-write-octets)))

(definterface fn-aj-host-recover
  :class ::ideal
  :keystones ((fn-aj-recover-past-profile-is-named :via fn-aj-recover-record)))

(definterface fn-aj-host-max-record-length
  :class ::ideal)
(defun fn-aj-host-next-name (frontier)
  (if (fn-aj-statep frontier)
      (fn-aj-record-name (fn-aj-domain frontier) (fn-aj-next frontier))
    nil))

(definterface fn-aj-host-next-name
  :class ::ideal)

(definterface fn-aj-host-authorize
  :class ::ideal
  :keystones ((fn-aj-reserved-resolution-fits :via fn-aj-authorize)))
(defun fn-aj-host-operationp (operation)
  (if (fn-aj-operationp operation) t nil))

(definterface fn-aj-host-operationp
  :class ::ideal)

(definterface fn-aj-host-operation-name
  :class ::ideal)

(definterface fn-aj-host-operation-label
  :class ::ideal)

(definterface fn-aj-host-operation-publication
  :class ::ideal)

(definterface fn-aj-host-operation-successor
  :class ::ideal)
