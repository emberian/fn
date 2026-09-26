; fn: a peer boundary's opaque-carriage budget as typed configuration rows
; (PRF-099; review 2026-09-24, gpt-6 direction: "Permit [unknown-author
; carriage] only under an explicit peer/group/byte policy").
;
; A boundary that carries principals this node has not enrolled (D23, the
; `carries-principal' rows books/peer-authored-accept.lisp reads) holds their
; articles against a budget of its own: two rows of the peer's configuration
; group whose natural slot is typed by the row recognizer (`fn-cfg-rowp':
; uint32), not a decimal string,
;
;   (name "carried-budget-charge" "" CHARGE)   ; Store charge units
;   (name "carried-budget-count"  "" COUNT)    ; carried articles
;
; CHARGE is in the Store's own resource unit, the one the retention capacity
; and the quotas use (`fn-charge-for-payload', books/identity.lisp: one unit
; per started 4096-octet page plus one), so the row width is the capacity's
; width and never caps below a store the operator can write (D27).  The
; operator's verb takes octets and rounds down to whole pages
; (books/native-admin-peer.lisp `peer budget NAME OCTETS COUNT').  A peer
; with no budget rows has no budget, and the carried arm then admits nothing
; (books/peer-carriage.lisp `fn-pcb-admission').
;
; This book is the rows alone (config only), so the operator's parser and the
; acceptance decision read one spelling.  It also owns the merge that lets a
; boundary's carried list and budget change across requests: the operator's
; argv bound stays a per-request work bound (D27) and a list longer than one
; request grows by `peer carries NAME HEX ...' requests.
(in-package "ACL2")
(include-book "config")

(defconst *fn-pcb-charge-slot* "carried-budget-charge")
(defconst *fn-pcb-count-slot* "carried-budget-count")

; The natural of the first row whose slot is SLOT, or nil.
(defun fn-pcb-slot-natural (slot rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-cfg-row-b (car rows)) slot)
          (if (natp (fn-cfg-row-n (car rows))) (fn-cfg-row-n (car rows)) nil)
        (fn-pcb-slot-natural slot (cdr rows)))
    nil))

(defun fn-pcb-budgetp (budget)
  (declare (xargs :guard t))
  (and (true-listp budget) (equal (len budget) 2)
       (natp (car budget)) (natp (cadr budget))))

; (CHARGE COUNT) when both rows are present, else nil: no budget.
(defun fn-pcb-budget-of-rows (rows)
  (declare (xargs :guard t))
  (let ((charge (fn-pcb-slot-natural *fn-pcb-charge-slot* rows))
        (count (fn-pcb-slot-natural *fn-pcb-count-slot* rows)))
    (if (and (natp charge) (natp count)) (list charge count) nil)))

; The delivering boundary's budget: its rows in the configured peer table.
(defun fn-pcb-peer-budget (peer peers)
  (declare (xargs :guard t))
  (fn-pcb-budget-of-rows (fn-cfg-rows-with-key peers peer)))

(defthm fn-pcb-peer-budget-is-typed-or-absent
  (let ((b (fn-pcb-peer-budget peer peers)))
    (or (null b) (fn-pcb-budgetp b)))
  :rule-classes nil)

(defun fn-pcb-budget-rows (name charge count)
  (declare (xargs :guard t))
  (list (fn-cfg-row-make name *fn-pcb-charge-slot* "" charge)
        (fn-cfg-row-make name *fn-pcb-count-slot* "" count)))

; -----------------------------------------------------------------------------
; Growing a boundary's rows across requests.  NEW replaces the existing
; budget rows when it carries a budget slot, and appends every row not
; already present; nothing else of the peer's group changes.

; The peer's NEWNEWS pull interval in seconds (PRF-100, books/peer-pull.lisp;
; `peer pull NAME SECONDS').  Single-valued like the budget rows, so a new
; interval supersedes the old one on extension.
(defconst *fn-pcb-pull-interval-slot* "pull-interval")

; How many consecutive complete rounds an id the peer lists but answers 430
; holds the pull cursor (PRF-165, books/peer-pull.lisp; `peer pull NAME
; SECONDS ROUNDS').  Single-valued; absent means the book's policy default.
(defconst *fn-pcb-pull-unavailable-slot* "pull-unavailable-rounds")

(defun fn-pcb-budget-slotp (slot)
  ; The single-valued slots: a new row replaces the old one on extension.
  (declare (xargs :guard t))
  (or (equal slot *fn-pcb-charge-slot*) (equal slot *fn-pcb-count-slot*)
      (equal slot *fn-pcb-pull-interval-slot*)
      (equal slot *fn-pcb-pull-unavailable-slot*)))

(defun fn-pcb-slot-memberp (slot rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (or (equal (fn-cfg-row-b (car rows)) slot)
          (fn-pcb-slot-memberp slot (cdr rows)))
    nil))

(defun fn-pcb-row-supersededp (row new)
  (declare (xargs :guard t))
  (or (and (member-equal row (if (true-listp new) new nil)) t)
      (and (fn-pcb-budget-slotp (fn-cfg-row-b row))
           (fn-pcb-slot-memberp (fn-cfg-row-b row) new))))

(defun fn-pcb-kept-rows (existing new)
  (declare (xargs :guard t))
  (if (consp existing)
      (if (fn-pcb-row-supersededp (car existing) new)
          (fn-pcb-kept-rows (cdr existing) new)
        (cons (car existing) (fn-pcb-kept-rows (cdr existing) new)))
    nil))

(defun fn-pcb-extend-rows (existing new)
  (declare (xargs :guard t))
  (append (fn-pcb-kept-rows existing new) (if (true-listp new) new nil)))

; The (:set-peer NAME ROWS) delta that extends NAME's group in PEERS by NEW,
; or nil when PEERS has no such peer (an extension never creates a peer).
(defun fn-pcb-extend-delta (name new peers)
  (declare (xargs :guard t))
  (let ((existing (fn-cfg-rows-with-key peers name)))
    (if (and (consp existing) (consp new))
        (fn-cfg-set-peer name (fn-pcb-extend-rows existing new))
      nil)))

; -----------------------------------------------------------------------------
; The admission theorem for the operator's budget rows.

(local (defthm fn-pcb-slot-natural-of-append
  (equal (fn-pcb-slot-natural slot (append a b))
         (if (fn-pcb-slot-memberp slot a)
             (fn-pcb-slot-natural slot a)
           (fn-pcb-slot-natural slot b)))))

(local (defthm fn-pcb-kept-rows-drop-new-budget-slots
  (implies (and (fn-pcb-budget-slotp slot) (fn-pcb-slot-memberp slot new))
           (not (fn-pcb-slot-memberp slot (fn-pcb-kept-rows existing new))))))

; KEYSTONE (the budget rows mean what the operator wrote).  Whatever rows the
; boundary had, extending them by `fn-pcb-budget-rows' makes the budget
; reader answer exactly (CHARGE COUNT).
(defthm fn-pcb-budget-after-extension
  (implies (and (natp charge) (natp count))
           (equal (fn-pcb-budget-of-rows
                   (fn-pcb-extend-rows existing
                                       (fn-pcb-budget-rows name charge count)))
                  (list charge count))))

(local (in-theory (enable fn-cfg-rows-with-key fn-cfg-rows-without-key
                          fn-cfg-rows-keyed-p)))

(local (defthm fn-pcb-rows-with-key-of-append
  (equal (fn-cfg-rows-with-key (append a b) k)
         (append (fn-cfg-rows-with-key a k) (fn-cfg-rows-with-key b k)))))

(local (defthm fn-pcb-rows-with-key-of-without-key
  (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows k) k) nil)))

(local (defthm fn-pcb-kept-rows-of-keyed
  (implies (fn-cfg-rows-keyed-p existing k)
           (fn-cfg-rows-keyed-p (fn-pcb-kept-rows existing new) k))))

(local (defthm fn-pcb-rows-keyed-of-append
  (equal (fn-cfg-rows-keyed-p (append a b) k)
         (and (fn-cfg-rows-keyed-p a k) (fn-cfg-rows-keyed-p b k)))))

(local (defthm fn-pcb-rows-with-key-is-keyed
  (fn-cfg-rows-keyed-p (fn-cfg-rows-with-key rows k) k)))

(local (defthm fn-pcb-rows-with-key-when-keyed
  (implies (and (fn-cfg-rows-keyed-p rows k) (true-listp rows))
           (equal (fn-cfg-rows-with-key rows k) rows))))

(local (defthm fn-pcb-budget-rows-keyed
  (fn-cfg-rows-keyed-p (fn-pcb-budget-rows name charge count) name)))

(local (defthm fn-pcb-true-listp-of-kept-rows
  (true-listp (fn-pcb-kept-rows existing new))))

(local
(defthm fn-pcb-rows-with-key-of-extend-rows
  (implies (and (fn-cfg-rows-keyed-p existing k)
                (fn-cfg-rows-keyed-p new k))
           (equal (fn-cfg-rows-with-key (fn-pcb-extend-rows existing new) k)
                  (fn-pcb-extend-rows existing new)))
  :hints (("Goal" :in-theory (enable fn-pcb-extend-rows)))))

; KEYSTONE (over the configuration the owner publishes).  When the named
; boundary exists, applying the extension delta with the operator's budget
; rows leaves exactly that budget under the boundary's name.
(defthm fn-pcb-peer-budget-after-extend-delta
  (implies (and (natp charge) (natp count)
                (consp (fn-cfg-rows-with-key (fn-cfg-peers v) name)))
           (equal (fn-pcb-peer-budget
                   name
                   (fn-cfg-peers
                    (fn-cfg-apply-delta
                     v gen stamp
                     (fn-pcb-extend-delta name
                                          (fn-pcb-budget-rows name charge count)
                                          (fn-cfg-peers v)))))
                  (list charge count)))
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply-delta fn-cfg-set-peer)
                                  (fn-pcb-budget-of-rows fn-pcb-extend-rows
                                   fn-pcb-budget-rows))
           :use ((:instance fn-pcb-budget-after-extension
                            (existing (fn-cfg-rows-with-key (fn-cfg-peers v)
                                                            name)))))))

(in-theory (disable fn-pcb-slot-natural fn-pcb-budget-of-rows
                    fn-pcb-kept-rows fn-pcb-extend-rows))
