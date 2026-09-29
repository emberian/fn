; fn: the external observer of the served POST's success (lane
; productive-contract, 2026-09-29; PRF-1003; specs/productive-contract.md
; section 6).
;
; fn-pcx-post-productive (books/productive-contract.lisp) and
; fn-own-240-follows-consumed-completion name the successful outcome by the
; effects fn-served-post-outcome produces.  What a client sees is the octets
; the host writes: fn-served-reply-octets of those effects, the projection
; host/native/owner.lisp takes of every served result.  This book connects
; the two: for a served connection whose session is the POST-composed one,
; the reply octets of the :durable outcome are exactly the 240 line, and
; the outside-in suite's observation (tests/test_native_outside_in.py,
; test_a06_post_to_a_group: expect("240")) reads that line's first three
; octets.  Nothing else in the served path produces a 240
; (fn-post-outcome-240-only-for-a-durable-observation, books/nntp-post.lisp).
;
; This book shares the prefix `fn-pcx-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "served")

; RFC 3977 section 6.3.1: 240; the text is fn's (fn-proto-text "POST"
; :received, books/nntp-post.lisp), then CRLF.
(defconst *fn-pcx-240-line*
  (append (fn-nntp-string-octets "240 article received OK") '(13 10)))

(local
 (defthm fn-pcx-inj-nth-1-of-cons
   (equal (fn-inj-nth 1 (cons a (cons b c))) b)
   :hints (("Goal" :expand ((fn-inj-nth 1 (cons a (cons b c))) (fn-inj-nth 0 (cons b c)))
            :in-theory (enable fn-inj-nth fn-inj-car fn-inj-cdr)))))

; KEYSTONE (PRF-1003).  The octets on the wire for the durable outcome of a
; POST-composed session are the 240 line.  The hypothesis is the session
; shape fn-nntp-post-outcome tests (a non-POST session is answered the
; malformed-session line, never 240); fn-auth-post-session is the named
; projection two wrappers down (books/nntp-auth.lisp).
(defthm fn-pcx-observer-240
  (implies (fn-post-sessionp (fn-auth-post-session (fn-served-conn-session conn)))
           (equal (fn-served-reply-octets
                   (fn-served-result-effects (fn-served-post-outcome conn :durable)))
                  *fn-pcx-240-line*))
  :hints (("Goal" :in-theory (e/d (fn-served-post-outcome fn-nntp-post-outcome fn-post-single
                                   fn-post-result-effects fn-post-make-result fn-served-reply-octets
                                   fn-served-result-effects fn-served-make-result
                                   fn-nntp-single fn-nntp-make-result fn-nntp-result-effects
                                   fn-nntp-reply-effect fn-nntp-crlf fn-nntp-string-octets)
                                  (fn-post-sessionp fn-served-conn-session fn-inj-nth)))))

; The observation the outside-in test makes: the first three octets.
(defthm fn-pcx-observer-240-code
  (implies (fn-post-sessionp (fn-auth-post-session (fn-served-conn-session conn)))
           (equal (take 3 (fn-served-reply-octets
                           (fn-served-result-effects (fn-served-post-outcome conn :durable))))
                  (fn-nntp-string-octets "240")))
  :hints (("Goal" :use (fn-pcx-observer-240)
           :in-theory (disable fn-pcx-observer-240 fn-served-post-outcome fn-served-reply-octets))))
