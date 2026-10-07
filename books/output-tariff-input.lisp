; fn: the tariff of the gate's non-command first events (lane tariff4,
; 2026-10-06; the preview kinds of books/output-command-admission.lisp
; fn-ocap-preview other than :extension, which the served step's extension
; arms answer).
;
; The admission gate classifies the wire scanner's FIRST framed event, not
; only commands: a closed connection (:closed), a line still in progress
; (:partial-input), a line the scanner framed but the reader machine
; refuses as syntax (:protocol-error) and the body a POST, IHAVE or
; TAKETHIS began (:article-input).  Each is priced here from the reply the
; machine below the gate emits for that event:
;
;   :closed         none: the reader step of a session that is not open
;                   carries no effect (fn-nntp-step-pinned's first arm).
;   :partial-input  none: the scanner framed no event, so the machine is
;                   not entered and no reply exists until the line
;                   completes -- the completed event is priced under its
;                   own family.  The row prices 0.
;   :protocol-error the one 501 literal of the reader step's syntax arms
;                   (books/nntp.lisp fn-nntp-step-pinned; "501 syntax
;                   error", RFC 3977 section 3.2.1), within the session
;                   line.
;   :article-input  nil while the body is taken (the durable outcome is a
;                   separate event) or one refusal literal line, and the
;                   outcome event's own line, all within the article line
;                   (books/nntp-post.lisp fn-nntp-post-step,
;                   fn-nntp-post-outcome).  The POST refusal texts are the
;                   long literals of the protocol table (the longest,
;                   :refused-approval-not-moderator, is 115 octets) and the
;                   store refusal lines run longer still, so this family
;                   has its own figure, not the session line's 64.
;
; The tariff multiplies the bound by the line figure
; (books/output-tariff-line.lisp); the cells-an-octet figure is stated, not
; derived (PGO-TARIFF-LINE-REPLY-CONSES, as for every line row).
(in-package "ACL2")
(include-book "output-tariff-auth")

; The article-input line: the longest reply the family answers is the store
; refusal for a group whose charge cannot be paid, 199 octets of text plus
; CRLF = 201 (books/nntp-post.lisp fn-post-store-refusal-text :unaffordable;
; the longest injection refusal literal is 117 with CRLF).
(defconst *fn-tariff-article-line-octets* 201)

; A closed reader session answers nothing: the step's effects are nil.
(defthm fn-tariff-closed-step-has-no-reply
  (implies (not (equal (fn-nntp-session-openp session) t))
           (equal (fn-nntp-result-effects
                   (fn-nntp-step-pinned session archive index verdicts env
                                       wire-event fn-arena))
                  nil))
  :hints (("Goal" :in-theory (enable fn-nntp-step-pinned))))

; A wire event that is not a command, or a command line that is not
; command input, is answered by the one 501 literal.  A well-formed
; command line is left to its family's own row.
(defthm fn-tariff-syntax-reply-within
  (implies (and (equal (fn-nntp-session-openp session) t)
                (not (and (consp wire-event)
                          (equal (car wire-event) :command)
                          (fn-nntp-command-inputp (fn-ocap-at 1 wire-event)))))
           (<= (fn-tariff-effects-octets
                (fn-nntp-result-effects
                 (fn-nntp-step-pinned session archive index verdicts env
                                     wire-event fn-arena)))
               *fn-tariff-session-line-octets*))
  :hints (("Goal" :in-theory (e/d (fn-nntp-step-pinned fn-nntp-single
                                    fn-nntp-make-result fn-nntp-result-effects
                                    fn-nntp-reply-effect fn-tariff-effects-octets)
                                  (fn-nntp-command-pinned)))))

; The refusal line is bounded ONCE, here, over every injection reason the
; decision can name (the cond's thirty arms are each a table literal, so
; this is computation per arm); the main theorems below keep
; fn-post-refusal-line DISABLED so no reason case ever expands there.
; This is the one lemma that pays for the family's case explosion.
(local
 (defthm fn-tariff-post-refusal-line-within
   (<= (+ 2 (len (fn-nntp-string-octets (fn-post-refusal-line reason))))
       *fn-tariff-article-line-octets*)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-post-refusal-line)))))

; The store refusal lines, likewise once: each kind's text with the shared
; 441 prefix, the longest being :unaffordable's 199 octets.
(local
 (defthm fn-tariff-post-store-refusal-line-within
   (<= (+ 2 (len (fn-nntp-string-octets (fn-post-store-refusal-line kind))))
       *fn-tariff-article-line-octets*)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-post-store-refusal-line
                                      fn-post-store-refusal-text)))))

; A body a POST, IHAVE or TAKETHIS began: the immediate reply is nil (the
; article is taken; the durable outcome is a separate event) or one
; refusal literal line, whatever the wire event is.  fn-post-make-result
; and the accessors stay disabled: their rewrite theorems carry the
; effects out of the result record without exposing fn-inj-nth.
(defthm fn-tariff-article-input-reply-within
  (implies (fn-post-session-awaiting ps)
           (<= (fn-tariff-effects-octets
                (fn-post-result-effects
                 (fn-nntp-post-step ps archive config observation injection
                                   wire-event fn-arena)))
               *fn-tariff-article-line-octets*))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-post-step fn-post-single)
                           (fn-post-refusal-line
                            fn-post-gated-decision fn-post-body-octets
                            fn-inj-injectedp fn-inj-decision-reason
                            fn-inj-config-allow fn-post-offeredp)))))

; The durable outcome event's own line, one literal whatever the completion.
(defthm fn-tariff-post-outcome-reply-within
  (<= (fn-tariff-effects-octets
       (fn-post-result-effects (fn-nntp-post-outcome ps completion)))
      *fn-tariff-article-line-octets*)
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-post-outcome fn-post-single)
                           (fn-post-refusal-line fn-post-store-refusal-line
                            fn-post-store-refusalp)))))
