;; The connection machine fn2-conn (layer D, quest D3; ROUND2 section B.2
;; row 1, its connection half: the listener is A's fn2-listener). The design,
;; with every arm's contract, is docs/d-machines-nntp.md section 4.2.
;; Declared through defmachine with every arm in the checked arm language
;; (none :unchecked); the decision table is conn-answer.lisp; the grammar is
;; nntp-grammar.lisp. Schema and partition registration live in
;; books/conn-kind.lisp; continuations are materialized by
;; assembly-callbacks-d-conn.lisp.
(in-package "ACL2")
(include-book "conn-kind")
(include-book "upload-kind")
(fn2-book-layer :d)

;; Declared costs of the connection's outside calls (section 4.2). Each is a
;; thin stobj-let wrapper over a pool-level function; none builds a list.
(defcost fn2-conn-frame :bytes *fn2-conn-frame-bytes* :tables (fn2-core-pool)
  :doc "Frame RX from the row's (start pos overflow): the grammar's framer under the frame quantum.")
(defcost fn2-conn-run-answer :bytes *fn2-conn-answer-bytes*
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Parse one framed line and answer it into TX (conn-answer.lisp); reads the clock mailbox.")
(defcost fn2-conn-run-overflow :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render the overflow refusal into TX.")
(defcost fn2-conn-run-greeting :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render the greeting, or the capacity 400, into TX.")
(defcost fn2-conn-fill :doc "A held pool slot's fill.")
(defcost fn2-conn-reading-p :doc "Whether the profile serves reading: the cursor partition has rows.")
(defcost fn2-conn-cursor-go :tables (fn2-cursor-table) :doc "Give the query cursor its move (TX is empty).")
(defcost fn2-conn-cursor-cancel :tables (fn2-cursor-table) :doc "Cancel a waiting query cursor: the connection drains.")
(defcost fn2-conn-posting-p :doc "Whether posting is served (the input configuration; section 14.5).")
(defcost fn2-conn-peering-p :doc "Whether peers are admitted: the peer bit on a connection with an address family (the input configuration; E4's grant replaces it).")
(defcost fn2-conn-run-block-open :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render a block's opening reply (340) into TX.")
(defcost fn2-conn-run-outcome :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render a block's outcome reply into TX.")
(defcost fn2-conn-cap :doc "A held pool slot's capacity.")
(defcost fn2-conn-feed-run :bytes *fn2-conn-feed-cost*
  :answers (:terminator :need-more :budget :bounds :fault)
  :faults (:bounds :fault)
  :tables (fn2-core-pool)
  :doc "Feed RX into the upload's chunk (upload-feed.lisp).")

;; ------------------------------------------------------------------------
;; The operations are defined after the core instance in
;; assembly-callbacks-d.lisp. Pool accesses use the connection owner triple.
; The helpers are defined once in assembly-callbacks-d.lisp.

;; The connection's continuations (materialized in assembly-callbacks-d-conn.lisp).
(defmacro fn2-conn-events ()
 '(progn
(defmachine-arms fn2-conn)
(defmachine-run fn2-conn)
))
