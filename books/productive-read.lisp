; fn: the productive READ (lane productive-read-transfer, row W6b, 2026-09-30;
; PRF-1053 fn-pcr-served-read-is-the-reference-read, PRF-1054
; fn-pcr-retrieval-answers-220-with-the-stored-octets).
;
; DISCOVERY ADMISSIONS, NOT CERTIFICATION. Both statements were admitted in
; protected persvati REPL pcr61. The successor composition is in
; productive-read-chain.lisp, including an admitted complete numbered ARTICLE
; host-called read. Complete teeth, Message-ID/absent variants and union/native
; evidence remain open; neither book is a Makefile qualification root yet.
;
; THE SUBJECT (the function the host calls): fn-mca-read-span, which
; host/owner-host.lisp fn-owner-chunk-span-at calls for one served socket
; chunk [START, END) of fn-octets (host/native/owner.lisp fnn-owner-handle-chunk).
;
; THE COLD PAGE (row A4 (c), books/owner-time-bars.lisp section 2): a served
; line whose extent is not in memory is preread OFF the owner mutex
; (host/native/owner.lisp fnn-owner-cold-line, fnn-extent-prefetch); the
; host asks ACL2's fn-otb-dependency-step SINCE NOW LIMIT COMPLETED each
; wake: :serve (the page came: the read runs again, warm, through
; fn-owner-chunk-span-at), :unavailable (the deadline passed: the line is
; answered 403 by fn-owner-unavailable-line-at over fn-ocln-unavailable-span,
; never 430/423), or (:wait MS).  So the productive read with a cold page
; has TWO named premises the host establishes and ACL2 decides:
;   (1) the successful page completion: COMPLETED is true, so the dependency
;       step answers :serve (fn-otb-a-late-page-is-unavailable-never-absent);
;   (2) scheduling: the gate's scheduler value S admits the read
;       (fn-otm-admit-post S is not :shed), the credit funds it, the article
;       slots hold it, and no committer capture is live (VIEWS empty).
; The host's routing (":serve, then fn-owner-chunk-span-at") is Lisp in
; fnn-owner-cold-line: an external host I/O routing boundary; no named logical assumption is
; introduced here, and no ACL2 twin models that Lisp routing.
;
; THE CHAIN the lift composes (each link an existing equality):
;   fn-mca-read-span  = fn-oas-read-span   fn-mca-read-span-within-the-credit-unfolds (owner-credits)
;   fn-oas-read-span  = fn-otm-read-span   fn-oas-read-span-when-held-unfolds (owner-article-slots)
;   fn-otm-read-span  = fn-orr-read-span   fn-otm-read-span-when-admitted-unfolds (owner-time-admission)
;   fn-orr-read-span  = fn-scr-ocfg-read-span   fn-orr-read-span-without-a-capture-is-the-span-read-by-definition (owner-reader-read)
;   fn-scr-ocfg-read-span = fn-ocfg-read-tls-prefix over (fn-oct-slice-list i end fn-octets)
;                                          fn-scr-ocfg-read-span-is-reference-under-ocl-relation (served-catalog-chain)
;   fn-ocfg-read-tls-prefix's effects/owner = fn-ocfg-read of the consumed prefix
;                                          fn-ocfg-read-tls-prefix-is-read-of-consumed-prefix (owner-tls-prefix)
;   fn-ocfg-read = fn-own-read-full's projections (by definition; = fn-own-read's car)
;   fn-own-read  = fn-served-step on the pinned prefix   fn-own-read-is-served-step-on-pinned-prefix (owner-invariants-served)
; Below fn-served-step the ARTICLE line reaches the retrieval:
;   fn-served-step (byte fold) -> fn-served-dispatch -> fn-auth-step-pinned ->
;   peer -> post -> fn-nntp-step -> fn-nntp-command-pinned ->
;   fn-nntp-archive-command-pinned = fn-rcompat-retrieval (PRF-243,
;   fn-nntp-archive-command-pinned-article-head-is-served, nntp-pinned-msgid)
; This lower book does not itself establish the protocol/wire joins.
; productive-read-chain.lisp admits those actual joins and the full numbered
; host read; the remaining witness/variant/evidence work stays explicit.

(in-package "ACL2")
(include-book "owner-credits")
(include-book "owner-cold-line")
(include-book "owner-tls-prefix")
(include-book "owner-invariants-served")
(include-book "nntp-pinned-msgid")

; -----------------------------------------------------------------------------
; PRF-1053.  The host-called reader entry, with a cold page that completed
; and the scheduler admitting, answers exactly the reference reader's
; answer on the connection's pinned archive after OVER cursor expansion:
; the expanded effects and the owner of
; fn-mca-read-span are those of fn-ocfg-read over the consumed prefix of the
; chunk, and the expanded effects are fn-own-read's.  Each premise is named; the
; funded / within-the-slots premises are stated in the shape the chain's
; own theorems state them (the credit resized to what the read needs
; answers :ok; the read does not put the connection over the slots).

(defthm fn-pcr-served-read-is-the-reference-read
  (let* ((o (fn-ocfg-owner oc))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (rc (fn-mca-read-span credits oc views id i end cache s slots reserve
                               fn-octets fn-arena fn-cat))
         (result (car rc))
         (octets (fn-oct-slice-list i end fn-octets))
         (consumed (fn-own-tls-result-consumed result))
         (reference (fn-ocfg-read oc id (take consumed octets) fn-arena)))
    (implies (and completed
                  (equal (car (fn-mcr-resize
                               credits (fn-mca-conn-key id)
                               (fn-mca-need (fn-own-tls-result-owner
                                             (fn-oas-read-span oc views id i end cache s slots
                                                               fn-octets fn-arena fn-cat))
                                            id reserve)))
                         :ok)
                  (not (fn-oas-over-p oc (fn-own-tls-result-owner
                                          (fn-otm-read-span oc views id i end cache s
                                                            fn-octets fn-arena fn-cat))
                                      id slots))
                  (not (eq (fn-otm-admit-post s) :shed))
                  (not (consp views))
                  (fn-gacc-okp cache) (fn-ocl-relation oc)
                  (fn-scar-view-indexedp o)
                  (fn-scr-owner-catalogp o id fn-arena fn-cat)
                  (fn-scol-okp fn-arena fn-cat)
                  (natp i) (natp end)
                  (fn-wire-statep (fn-own-conn-wire conn)))
             (and (equal (fn-otb-dependency-step since now limit completed) :serve)
                  (equal (fn-ovw-expand (fn-own-tls-result-effects result) fn-arena fn-cat)
                         (fn-ovw-expand (car reference) fn-arena fn-cat))
                  (equal (fn-own-tls-result-owner result) (cdr reference))
                  (equal (fn-ovw-expand (fn-own-tls-result-effects result) fn-arena fn-cat)
                         (fn-ovw-expand
                          (car (fn-own-read o id (take consumed octets) fn-arena))
                          fn-arena fn-cat)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-mca-read-span-within-the-credit-unfolds
                 fn-oas-read-span-when-held-unfolds
                 fn-otm-read-span-when-admitted-unfolds
                 fn-orr-read-span-without-a-capture-is-the-span-read-by-definition
                 fn-scr-ocfg-read-span-is-reference-under-ocl-relation
                 (:instance fn-ocfg-read-tls-prefix-is-read-of-consumed-prefix
                            (octets (fn-oct-slice-list i end fn-octets)))
                 fn-otb-a-late-page-is-unavailable-never-absent)
           :in-theory (union-theories '(fn-ocfg-read fn-own-read car-cons cdr-cons)
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; PRF-1054.  The served retrieval of a PRESENT article by number is the 220
; line and the dot-stuffed block of the article's served octets: the stored
; octets (fn-nntp-article-bytes, read through the arena) with the Xref line
; the server inserts when the article carries Xref pairs (RFC 5536
; section 3.2.14; fn-rcompat-served-payload-of-bytes) -- exactly the stored
; octets when it carries none.  The subject fn-rcompat-retrieval is what
; fn-nntp-archive-command-pinned IS for ARTICLE (PRF-243).

(defun fn-pcr-served-octets (server article fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-rcompat-served-payload-of-bytes server article (fn-nntp-article-bytes article fn-arena)))

(defun fn-pcr-220-reply (session article number group server fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-nntp-make-result
   (fn-nntp-set-cursor session group number)
   (list (fn-nntp-reply-effect
          (append (fn-nntp-crlf (fn-nntp-retrieval-initial :article number article))
                  (fn-nntp-stuff-lines
                   (car (cdr (fn-nntp-crlf-lines (fn-pcr-served-octets server article fn-arena)))))
                  '(46 13 10))))))

(defthm fn-pcr-retrieval-answers-220-with-the-stored-octets
  (let* ((group (fn-nntp-session-group session))
         (number (fn-nntp-decimal-value token))
         (article (fn-nntp-find-group-number group number (fn-state-articles archive)))
         (served (fn-pcr-served-octets server article fn-arena)))
    (implies (and (fn-arena-p fn-arena)
                  (fn-nntp-number-tokenp token)
                  group
                  (consp article)
                  (fn-nntp-response-okp-of-bytes article
                     (fn-nntp-article-bytes article fn-arena) :article)
                  (fn-nntp-response-okp-of-bytes article served :article))
             (equal (fn-rcompat-retrieval session archive trie :article (list token) server fn-arena)
                    (fn-pcr-220-reply session article number group server fn-arena))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-rcompat-article-reply-exec-is-the-reply
                            (number (fn-nntp-decimal-value token)) (kind :article) (updatep t)
                            (group (fn-nntp-session-group session))
                            (article (fn-nntp-find-group-number
                                      (fn-nntp-session-group session)
                                      (fn-nntp-decimal-value token) (fn-state-articles archive))))
                 (:instance fn-nntp-response-of-bytes-session
                            (number (fn-nntp-decimal-value token)) (kind :article) (updatep t)
                            (group (fn-nntp-session-group session))
                            (article (fn-nntp-find-group-number
                                      (fn-nntp-session-group session)
                                      (fn-nntp-decimal-value token) (fn-state-articles archive)))
                            (bytes (fn-pcr-served-octets
                                    server
                                    (fn-nntp-find-group-number
                                     (fn-nntp-session-group session)
                                     (fn-nntp-decimal-value token) (fn-state-articles archive))
                                    fn-arena))))
           :in-theory (e/d (fn-rcompat-retrieval fn-rcompat-article-reply-exec
                            fn-nntp-article-response-of-bytes fn-nntp-response-okp-of-bytes
                            fn-nntp-section-of-bytes fn-pcr-served-octets fn-pcr-220-reply)
                           (fn-rcompat-article-reply fn-rcompat-served-payload-of-bytes
                            fn-nntp-article-bytes fn-nntp-crlf-lines fn-nntp-stuff-lines
                            fn-nntp-retrieval-initial fn-nntp-set-cursor fn-nntp-make-result
                            fn-nntp-reply-effect fn-nntp-find-group-number fn-nntp-single
                            fn-nntp-framed-of-bytes fn-rcl-tombstonep fn-nntp-article-idp)))))

(in-theory (disable fn-pcr-served-octets fn-pcr-220-reply))

; The broad reference now compares expanded effects. These inversion facts
; recover exact ARTICLE effects: a cursor cannot expand to these replies.
(local
  (defthm
    fn-pcr-expand-is-empty-exactly
    (equal (equal (fn-ovw-expand effects fn-arena fn-cat) nil) (equal effects nil))
    :hints
    (("Goal"
       :expand
       ((fn-ovw-expand effects fn-arena fn-cat))
       :in-theory
       (disable fn-ovw-cursor-effectp fn-ovw-cursor-octets)))))

(defthm
  fn-pcr-expand-inverts-a-distinct-single-reply
  (implies
    (and
      (equal (fn-ovw-expand effects fn-arena fn-cat) (list (fn-nntp-reply-effect octets)))
      (not (equal (fn-ovw-cursor-octets (car (cdr (car effects))) fn-arena fn-cat) octets)))
    (equal effects (list (fn-nntp-reply-effect octets))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :expand
     ((fn-ovw-expand effects fn-arena fn-cat))
     :in-theory
     (e/d (fn-nntp-reply-effect) (fn-ovw-cursor-effectp fn-ovw-cursor-octets)))))

(defthm
  fn-pcr-over-cursor-never-expands-to-an-article-reply
  (let
    ((octets (fn-ovw-cursor-octets cur fn-arena fn-cat)))
    (and
      (not (equal octets (append (quote (50 50 48)) tail)))
      (not
        (equal
          octets
          (append (fn-nntp-string-octets "423 no article with that number") (quote (13 10)))))
      (not
        (equal
          octets
          (append (fn-nntp-string-octets "430 no article with that message-id") (quote (13 10)))))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :in-theory
     (e/d
       (fn-ovw-cursor-octets fn-ovw-reply fn-ovw-status fn-ovw-empty-text fn-nntp-crlf)
       (fn-ovw-lines fn-nntp-stuff-lines)))))

(defthm
  fn-pcr-expand-inverts-220-reply
  (implies
    (equal
      (fn-ovw-expand effects fn-arena fn-cat)
      (list (fn-nntp-reply-effect (append (quote (50 50 48)) tail))))
    (equal effects (list (fn-nntp-reply-effect (append (quote (50 50 48)) tail)))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :use
     ((:instance
        fn-pcr-expand-inverts-a-distinct-single-reply
        (octets (append (quote (50 50 48)) tail)))
       (:instance
         fn-pcr-over-cursor-never-expands-to-an-article-reply
         (cur (car (cdr (car effects))))))
     :in-theory
     (theory (quote minimal-theory)))))

(local
  (defthm
    fn-pcr-220-result-has-220-prefix-by-definition
    (equal
      (fn-nntp-result-effects (fn-pcr-220-reply session article number group server fn-arena))
      (list
        (fn-nntp-reply-effect
          (append
            (quote (50 50 48))
            (cdr
              (cdr
                (cdr
                  (car
                    (cdr
                      (car
                        (fn-nntp-result-effects
                          (fn-pcr-220-reply session article number group server fn-arena))))))))))))
    :rule-classes
    nil
    :hints
    (("Goal"
       :in-theory
       (e/d
         (fn-pcr-220-reply
           fn-nntp-result-effects
           fn-nntp-make-result
           fn-nntp-reply-effect
           fn-nntp-retrieval-initial
           fn-nntp-append-pieces
           fn-nntp-crlf)
         (fn-nntp-decimal-field
           fn-article-msgid
           fn-pcr-served-octets
           fn-nntp-stuff-lines
           fn-nntp-crlf-lines
           fn-nntp-set-cursor))))))

(defthm
  fn-pcr-expanded-numbered-220-is-the-raw-reply
  (implies
    (equal
      (fn-ovw-expand effects fn-arena fn-cat)
      (fn-ovw-expand
        (fn-nntp-result-effects (fn-pcr-220-reply session article number group server fn-arena))
        fn-arena
        fn-cat))
    (equal
      effects
      (fn-nntp-result-effects (fn-pcr-220-reply session article number group server fn-arena))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :use
     (fn-pcr-220-result-has-220-prefix-by-definition
       (:instance
         fn-pcr-expand-inverts-220-reply
         (tail
           (cdr
             (cdr
               (cdr
                 (car
                   (cdr
                     (car
                       (fn-nntp-result-effects
                         (fn-pcr-220-reply session article number group server fn-arena)))))))))))
     :in-theory
     (union-theories
       (quote (fn-ovw-expand-of-reply-cons fn-ovw-expand-of-nil))
       (theory (quote minimal-theory))))))
