; fn: the replay's intern parses each article ONCE (lane snapshot-open-3,
; 2026-09-27).  Prefix `fn-ipo-'.
;
; The full replay interns every decoded article (books/payload-extent.lisp
; fn-arx-intern-step -> fn-arx-cat-intern-extent): the held row's facts
; (books/catalog-record.lisp fn-held-facts-of: the control fact,
; fn-ctl-control-of, parses the article's header) and its context
; (fn-held-context-of: the verdict, fn-stx-verdict-of-octets, and the delta,
; fn-stx-delta, EACH parse it again through fn-stx-parse).  Three parses of
; one article: at 100k x 2 KiB they were 3,264 of the open's 16,650 CPU
; samples (planning/evidence/snapshot-open-3-2026-09-27.md, M2).
;
; Here the held row's facts and context come from ONE fn-article-parse
; (fn-ipo-facts-context: the three readers over that one result).  KEYSTONE
; fn-ipo-facts-context-is-facts-and-context: its two values ARE
; fn-held-facts-of and fn-held-context-of, no hypothesis.  The executable
; row builder of the extent intern (books/payload-extent.lisp
; fn-arx-cat-intern-extent, under mbe) calls it; the logic of the intern is
; unchanged, so every theorem of fn-arx-intern-step (PRF-294's
; fn-arx-steps-are-one-step-of-the-concatenation) is about the code the host
; runs (host/native/io.lisp fnn-bridge-recover-step-extents).

(in-package "ACL2")
(include-book "catalog-record")

; The facts and the context of an article's octets from one parse.
(defun fn-ipo-facts-context (bytes keyring generation)
  (declare (xargs :guard (and (true-listp bytes) (fn-prin-keyringp keyring) (natp generation))))
  (let* ((r (fn-article-parse bytes))
         (okp (fn-article-result-okp r))
         (article (and okp (fn-article-result-article r)))
         (fields (if (and okp (true-listp article)) (fn-article-fields article) nil))
         (a (if (and (true-listp r) okp (fn-article-syntax-p article)) article nil)))
    (mv (fn-hf-make (len bytes) (fn-hf-split-index bytes 0) (fn-hf-body-lines-of bytes)
                    (list (fn-ctl-article-target fields)
                          (fn-ctl-cancel-keys fields)
                          (fn-ctl-cancel-locks fields)))
        (fn-hc-make (if a
                        (fn-stx-verdict a keyring generation)
                      (fn-stx-make-verdict :unverified :malformed generation))
                    (if (and a (fn-stx-verifiedp a keyring))
                        (list (fn-stx-statement-of a))
                      nil)
                    generation))))

; KEYSTONE.
(defthm fn-ipo-facts-context-is-facts-and-context
  (equal (fn-ipo-facts-context bytes keyring generation)
         (list (fn-held-facts-of bytes)
               (fn-held-context-of bytes keyring generation)))
  :hints (("Goal" :in-theory (e/d (fn-held-facts-of fn-held-context-of fn-ctl-control-of
                                   fn-ctl-received-fields fn-stx-verdict-of-octets
                                   fn-stx-delta fn-stx-parse)
                                  (fn-article-parse fn-stx-verdict fn-hc-make fn-hf-make
                                   fn-stx-make-verdict fn-stx-verifiedp fn-stx-statement-of
                                   fn-ctl-article-target fn-ctl-cancel-keys
                                   fn-ctl-cancel-locks fn-hf-split-index
                                   fn-hf-body-lines-of fn-article-fields
                                   fn-article-syntax-p)))))


(in-theory (disable fn-ipo-facts-context))
