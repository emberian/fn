; Actual host-wrapper phase-refusal witness.  This source is loaded after
; host/owner-host.lisp because that wrapper is :program host code, not an
; ACL2 certification root.
(in-package "ACL2")

(assert-event (equal (fn-owner-feed-connect-timeout) 10))

(defconst *foch-stream* (fn-fc-initial-state t 7))
(defconst *foch-greeting-400*
  (fn-fc-step *foch-stream* '(52 48 48 32 110 111 13 10)))
(assert-event (equal (fn-fc-kind *foch-greeting-400*) :refused))
(assert-event
 (equal (fn-owner-feed-connection-result-kind *foch-greeting-400*)
        :connection-refused))

(defconst *foch-mode*
  (fn-fc-step *foch-stream* '(50 48 48 32 111 107 13 10)))
(assert-event (equal (fn-owner-feed-connection-result-kind *foch-mode*) :mode))
(defconst *foch-mode-500*
  (fn-fc-step (fn-fc-next-state *foch-mode*) '(53 48 48 32 110 111 13 10)))
(assert-event (equal (fn-fc-kind *foch-mode-500*) :refused))
(assert-event
 (equal (fn-owner-feed-connection-result-kind *foch-mode-500*)
        :connection-refused))

; A normal post-ready feed reply keeps its port-owned tag; only phase refusal
; is remapped, so a pending feed projection cannot be accidentally re-flushed.
(defconst *foch-ready*
  (fn-fc-step (fn-fc-next-state *foch-mode*) '(50 48 51 13 10)))
(defconst *foch-reply*
  (fn-fc-step (fn-fc-next-state *foch-ready*) '(50 51 56 13 10)))
(assert-event (equal (fn-owner-feed-connection-result-kind *foch-reply*) :reply))
