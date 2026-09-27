; fn: a slow or stalled disk refuses the POST command itself, 440, before
; the client sends the article (lane time-model-2, 2026-09-27, slice 2 of
; planning/design-time-model-2026-09-27.md section 3.4; PRF-315).
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
; The subject is fn-otm-read-span, which host/owner-host.lisp
; fn-owner-chunk-span-at calls with the admission the host read from the
; gate's value in the same quantum (host/native/owner.lisp
; fnn-owner-handle-chunk-read, after the read's :served clock event).
(in-package "ACL2")
(include-book "owner-time-model")
(include-book "owner-reader-read")

; The injection configuration with its posting bit set to ALLOW; the other
; fields as they are.
(defun fn-otm-cfg-with-allow (cfg allow)
  (declare (xargs :guard t))
  (if (consp cfg) (cons allow (cdr cfg)) (list allow)))

(defun fn-otm-owner-with-allow (oc allow)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (fn-ocfg-with-owner oc (fn-own-configure o (fn-otm-cfg-with-allow (fn-own-config o) allow)))))

; The served read, admitted or not.  ADMIT is fn-otm-admit-post's word.
(defun fn-otm-read-span (oc views id i end admit fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (if (eq admit :shed)
      (let ((result (fn-orr-read-span (fn-otm-owner-with-allow oc nil) views id i end
                                      fn-octets fn-arena fn-cat)))
        (fn-own-tls-make-result
         (fn-own-tls-result-consumed result)
         (fn-own-tls-result-effects result)
         (fn-otm-owner-with-allow (fn-own-tls-result-owner result)
                                  (fn-inj-config-allow (fn-own-config (fn-ocfg-owner oc))))
         (fn-own-tls-result-repinned result)))
    (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat)))

;; Admitted, the read is the reader read exactly: every theorem about
;; fn-orr-read-span (PRF-288, PRF-296) is a theorem about the host's call.
(defthm fn-otm-read-span-when-admitted-unfolds
  (implies (not (eq admit :shed))
           (equal (fn-otm-read-span oc views id i end admit fn-octets fn-arena fn-cat)
                  (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat))))

(defthm fn-otm-cfg-with-allow-allow
  (equal (fn-inj-config-allow (fn-otm-cfg-with-allow cfg allow)) allow)
  :hints (("Goal" :in-theory (enable fn-inj-config-allow fn-inj-nth fn-inj-car))))

(local
 (defthm fn-otm-own-config-of-configure
   (equal (fn-own-config (fn-own-configure o config)) config)
   :hints (("Goal" :in-theory (enable fn-own-config fn-own-configure fn-own-make)))))

(local
 (defthm fn-otm-ocfg-owner-of-with-owner
   (equal (fn-ocfg-owner (fn-ocfg-with-owner oc o)) o)
   :hints (("Goal" :in-theory (enable fn-ocfg-owner fn-ocfg-with-owner fn-ocfg-make)))))

(defthm fn-otm-owner-with-allow-allow
  (equal (fn-inj-config-allow (fn-own-config (fn-ocfg-owner (fn-otm-owner-with-allow oc allow))))
         allow)
  :hints (("Goal" :in-theory (disable fn-otm-cfg-with-allow))))

;; KEYSTONE (PRF-315, slice 2: 440 at the command).  While the disk sheds,
;; the served read runs with posting not permitted, and the owner it leaves
;; has the posting bit it had before: the slow disk changes what this read
;; answers, never the node's configuration.
(defthm fn-otm-read-span-while-shedding
  (implies (eq admit :shed)
           (let ((r (fn-otm-read-span oc views id i end admit fn-octets fn-arena fn-cat)))
             (and (not (fn-inj-config-allow
                        (fn-own-config (fn-ocfg-owner (fn-otm-owner-with-allow oc nil)))))
                  (equal (fn-inj-config-allow
                          (fn-own-config (fn-ocfg-owner (fn-own-tls-result-owner r))))
                         (fn-inj-config-allow (fn-own-config (fn-ocfg-owner oc))))
                  (equal (fn-own-tls-result-effects r)
                         (fn-own-tls-result-effects
                          (fn-orr-read-span (fn-otm-owner-with-allow oc nil) views id i end
                                            fn-octets fn-arena fn-cat))))))
  :hints (("Goal" :in-theory (disable fn-otm-owner-with-allow fn-otm-cfg-with-allow
                                      fn-orr-read-span))))

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

(in-theory (disable fn-otm-read-span fn-otm-owner-with-allow))
