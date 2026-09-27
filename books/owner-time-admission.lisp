; fn: a slow or stalled disk refuses the POST command itself, 440, before
; the client sends the article (lane time-model-2, 2026-09-27, slice 2 of
; planning/design-time-model-2026-09-27.md section 3.4; PRF-323).
;
; Slice 1 refused a POST try-later AFTER its article (441, the queued
; submission shed).  RFC 3977 section 6.3.1 gives the initial response 440
; ("Posting not permitted") for a POST the server will not take now, so the
; client does not send an article for nothing.  The served machine already
; answers 440 at the command when the owner's injection configuration does
; not permit posting (books/served-catalog-chain.lisp fn-scr-post-step: the
; offered POST under (fn-inj-config-allow config) = nil).  So the served
; read, while the disk sheds (books/owner-time-model.lisp fn-otm-admit-post
; = :shed at the read's recorded time), runs over the owner's value with
; the posting bit off, and the bit is put back after it: the read is the
; read of a node that does not permit posting, and nothing else about the
; owner changes.  The configuration itself (durable, published) is never
; touched: the bit is the read's input, not a reconfiguration.
;
; The replies name the disk's reason (lane ax-fix/reply-text): the served
; machine's own 440 ("440 posting not permitted") and its 441 for an article
; refused under a closed posting bit are, in this read and only when the
; connection's own bit permitted posting, replaced by the time model's lines
; (books/owner-time-model.lisp fn-otm-shed-replies: "440 posting not
; permitted now; the disk is stalled (...), try again later" and the shed
; 441), which the host read from the same scheduler value as the admission.
;
; The subject is fn-otm-read-span, which host/owner-host.lisp
; fn-owner-chunk-span-at calls with the admission and the replies the host
; read from the gate's value in the same quantum (host/native/owner.lisp
; fnn-owner-handle-chunk-read, fnn-owner-read-admission, after the read's
; :served clock event).
(in-package "ACL2")
(include-book "owner-time-model")
(include-book "owner-reader-read")

; The injection configuration with its posting bit set to ALLOW; the other
; fields as they are.
(defun fn-otm-cfg-with-allow (cfg allow)
  (declare (xargs :guard t))
  (if (consp cfg) (cons allow (cdr cfg)) (list allow)))

; The served step reads the CONNECTION's injection configuration
; (books/owner.lisp fn-own-served-conn: fn-own-conn-config, the snapshot the
; connection holds), so the bit is set on connection ID's record; the owner
; and every other connection are as they were.
(defun fn-otm-conn-with-allow (c allow)
  (declare (xargs :guard t))
  (if (and (true-listp c) (< 6 (len c)))
      (update-nth 6 (fn-otm-cfg-with-allow (fn-own-conn-config c) allow) c)
    c))

(defun fn-otm-owner-with-allow (oc id allow)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (c (fn-own-find-conn id (fn-own-conns o))))
    (if c
        (fn-ocfg-with-owner
         oc (fn-own-set-conns o (fn-own-replace-conn (fn-otm-conn-with-allow c allow)
                                                     (fn-own-conns o))))
      oc)))

; The posting bit connection ID's read runs with.
(defun fn-otm-conn-allow (oc id)
  (declare (xargs :guard t))
  (fn-inj-config-allow
   (fn-own-conn-config (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))

; The served machine's two replies under a closed posting bit, as the read's
; effects carry them: the POST command's 440 (books/served-catalog-chain.lisp
; fn-scr-post-step; fn-otm-closed-posting-answers-the-generic-440 below) and
; the injection's 441 for :posting-disallowed (books/nntp-post.lisp
; fn-post-refusal-line).
(defconst *fn-otm-generic-440*
  (fn-nntp-reply-effect (fn-nntp-crlf (fn-nntp-string-octets "440 posting not permitted"))))
(defconst *fn-otm-generic-441*
  (fn-nntp-reply-effect
   (fn-nntp-crlf (fn-nntp-string-octets (fn-post-refusal-line :posting-disallowed)))))

; One effect with the disk's reason: REPLIES is fn-otm-shed-replies'
; (LINE-440 . LINE-441); every other effect is kept.
(defun fn-otm-disk-reply-effect (x replies)
  (declare (xargs :guard t))
  (cond ((not (consp replies)) x)
        ((equal x *fn-otm-generic-440*) (fn-nntp-reply-effect (car replies)))
        ((equal x *fn-otm-generic-441*) (fn-nntp-reply-effect (cdr replies)))
        (t x)))

(defun fn-otm-disk-reply-effects (effects replies)
  (declare (xargs :guard t))
  (if (consp effects)
      (cons (fn-otm-disk-reply-effect (car effects) replies)
            (fn-otm-disk-reply-effects (cdr effects) replies))
    nil))

; The served read, admitted or not.  ADMIT is fn-otm-admit-post's word and
; REPLIES fn-otm-shed-replies', both of one scheduler value.
(defun fn-otm-read-span (oc views id i end admit replies fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (if (eq admit :shed)
      (let* ((result (fn-orr-read-span (fn-otm-owner-with-allow oc id nil) views id i end
                                       fn-octets fn-arena fn-cat))
             (effects (fn-own-tls-result-effects result)))
        (fn-own-tls-make-result
         (fn-own-tls-result-consumed result)
         (if (fn-otm-conn-allow oc id)
             (fn-otm-disk-reply-effects effects replies)
           effects)
         (fn-otm-owner-with-allow (fn-own-tls-result-owner result) id
                                  (fn-otm-conn-allow oc id))
         (fn-own-tls-result-repinned result)))
    (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat)))

;; Admitted, the read is the reader read exactly: every theorem about
;; fn-orr-read-span (PRF-288, PRF-296) is a theorem about the host's call.
(defthm fn-otm-read-span-when-admitted-unfolds
  (implies (not (eq admit :shed))
           (equal (fn-otm-read-span oc views id i end admit replies fn-octets fn-arena fn-cat)
                  (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat))))

;; The rewrite is a map: the Nth effect is the Nth effect with the disk's
;; reason, and there are as many.
(defthm fn-otm-disk-reply-effects-is-a-map
  (and (equal (len (fn-otm-disk-reply-effects effects replies)) (len effects))
       (equal (nth n (fn-otm-disk-reply-effects effects replies))
              (if (< (nfix n) (len effects))
                  (fn-otm-disk-reply-effect (nth n effects) replies)
                nil)))
  :hints (("Goal" :in-theory (e/d (nth) (fn-otm-disk-reply-effect)))))

;; Only the two generic replies change, each to the line naming the disk's
;; reason; every other effect, and every effect when the disk admits (no
;; replies), is kept.
(defthm fn-otm-disk-reply-effect-cases
  (equal (fn-otm-disk-reply-effect x replies)
         (cond ((and (consp replies) (equal x *fn-otm-generic-440*))
                (list :reply (car replies)))
               ((and (consp replies) (equal x *fn-otm-generic-441*))
                (list :reply (cdr replies)))
               (t x)))
  :hints (("Goal" :in-theory (enable fn-nntp-reply-effect))))

;; The served machine's 440 under a closed posting bit is the one effect
;; *fn-otm-generic-440*: the rewrite above replaces exactly that reply.
(defthm fn-otm-closed-posting-answers-the-generic-440
  (implies (and (fn-post-sessionp ps)
                (not (fn-post-session-awaiting ps))
                (not (fn-inj-config-allow config))
                (fn-post-offeredp
                 (fn-nntp-result-effects
                  (fn-scr-step (fn-post-session-base ps) archive index verdicts
                               (fn-post-reader-env config observation)
                               wire-event v fn-arena fn-cat))))
           (equal (fn-post-result-effects
                   (fn-scr-post-step ps archive index verdicts config observation injection
                                     wire-event v fn-arena fn-cat))
                  (list *fn-otm-generic-440*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-post-step fn-post-single fn-nntp-single
                                fn-post-result-effects-of-fn-post-make-result
                                fn-nntp-result-effects fn-nntp-make-result
                                (:e fn-nntp-reply-effect) (:e fn-nntp-crlf)
                                (:e fn-nntp-string-octets) cdr-cons)
                              (theory 'minimal-theory)))))

;; ... and its 441 for :posting-disallowed (books/nntp-post.lisp: the
;; refusal is fn-post-single of fn-post-refusal-line) is *fn-otm-generic-441*.
(defthm fn-otm-posting-disallowed-refusal-is-the-generic-441
  (equal (fn-post-single ps (fn-post-refusal-line :posting-disallowed))
         (list *fn-otm-generic-441*))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
                              '(fn-post-single fn-nntp-single
                                fn-nntp-result-effects fn-nntp-make-result
                                (:e fn-nntp-reply-effect) (:e fn-nntp-crlf)
                                (:e fn-nntp-string-octets) (:e fn-post-refusal-line)
                                cdr-cons)
                              (theory 'minimal-theory)))))

(defthm fn-otm-cfg-with-allow-allow
  (equal (fn-inj-config-allow (fn-otm-cfg-with-allow cfg allow)) allow)
  :hints (("Goal" :in-theory (enable fn-inj-config-allow fn-inj-nth fn-inj-car))))

(local
 (defthm fn-otm-ocfg-owner-of-with-owner
   (equal (fn-ocfg-owner (fn-ocfg-with-owner oc o)) o)
   :hints (("Goal" :in-theory (enable fn-ocfg-owner fn-ocfg-with-owner fn-ocfg-make)))))

(local
 (defthm fn-otm-conns-of-set-conns
   (equal (fn-own-conns (fn-own-set-conns o conns)) conns)
   :hints (("Goal" :in-theory (enable fn-own-conns fn-own-set-conns fn-own-make)))))

(local
 (defthm fn-otm-conn-with-allow-id-and-config
   (and (equal (fn-own-conn-id (fn-otm-conn-with-allow c allow)) (fn-own-conn-id c))
        (implies (and (true-listp c) (< 6 (len c)))
                 (equal (fn-own-conn-config (fn-otm-conn-with-allow c allow))
                        (fn-otm-cfg-with-allow (fn-own-conn-config c) allow))))
   :hints (("Goal" :in-theory (enable fn-own-conn-id fn-own-conn-config update-nth)))))

(local
 (defthm fn-otm-find-conn-of-replace-same
   (implies (and (fn-own-find-conn id conns) (equal (fn-own-conn-id c) id))
            (equal (fn-own-find-conn id (fn-own-replace-conn c conns)) c))
   :hints (("Goal" :in-theory (enable fn-own-find-conn fn-own-replace-conn)))))

(local
 (defthm fn-otm-find-conn-id
   (implies (fn-own-find-conn id conns)
            (equal (fn-own-conn-id (fn-own-find-conn id conns)) id))
   :hints (("Goal" :in-theory (enable fn-own-find-conn)))))

;; KEYSTONE (PRF-323, slice 2: 440 at the command).  Connection ID's read
;; while the disk sheds runs with posting not permitted (when its record has
;; the shape the owner makes, fn-own-conn-shapep); its effects are that
;; read's, with the disk's reason in the 440 and 441 when the connection's
;; own bit permitted posting (fn-otm-disk-reply-effects); and afterwards the connection, if still open, has the posting bit
;; it had before.  The slow disk changes what this read answers, never the
;; node's or the connection's configuration.
(defthm fn-otm-read-span-while-shedding
  (implies (eq admit :shed)
           (let ((r (fn-otm-read-span oc views id i end admit replies fn-octets fn-arena fn-cat))
                 (c (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
             (and (implies (and c (fn-own-conn-shapep c))
                           (not (fn-otm-conn-allow (fn-otm-owner-with-allow oc id nil) id)))
                  (implies (fn-own-conn-shapep
                            (fn-own-find-conn id (fn-own-conns
                                                  (fn-ocfg-owner
                                                   (fn-own-tls-result-owner
                                                    (fn-orr-read-span
                                                     (fn-otm-owner-with-allow oc id nil) views id i end
                                                     fn-octets fn-arena fn-cat))))))
                           (equal (fn-otm-conn-allow (fn-own-tls-result-owner r) id)
                                  (fn-otm-conn-allow oc id)))
                  (equal (fn-own-tls-result-effects r)
                         (let ((effects (fn-own-tls-result-effects
                                         (fn-orr-read-span (fn-otm-owner-with-allow oc id nil)
                                                           views id i end
                                                           fn-octets fn-arena fn-cat))))
                           (if (fn-otm-conn-allow oc id)
                               (fn-otm-disk-reply-effects effects replies)
                             effects))))))
  :hints (("Goal" :in-theory (e/d (fn-otm-read-span fn-otm-owner-with-allow fn-otm-conn-allow
                                   fn-own-conn-shapep)
                                  (fn-otm-cfg-with-allow fn-orr-read-span fn-own-find-conn
                                   fn-own-replace-conn fn-otm-conn-with-allow
                                   fn-otm-disk-reply-effects)))))

;; The command step under a configuration that does not permit posting:
;; a POST is never offered -- the session never awaits an article -- so no
;; article is read and nothing is submitted; RFC 3977 section 6.3.1's 440
;; is the reply fn-scr-post-step renders.
(defthm fn-otm-closed-posting-never-awaits-an-article
  (implies (and (fn-post-sessionp ps)
                (not (fn-post-session-awaiting ps))
                (not (fn-inj-config-allow config)))
           (not (fn-post-session-awaiting
                 (fn-post-result-session
                  (fn-scr-post-step ps archive index verdicts config observation injection
                                    wire-event v fn-arena fn-cat)))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scr-post-step
                                fn-post-result-session-of-fn-post-make-result
                                fn-post-session-awaiting-of-fn-post-make-session)
                              (theory 'minimal-theory)))))

(in-theory (disable fn-otm-read-span fn-otm-owner-with-allow fn-otm-conn-allow
                    fn-otm-disk-reply-effect fn-otm-disk-reply-effects))
