; Teeth for books/owner-feed-article (lane feed-fault, 2026-09-27).
;
; The witness Store is acceptance-payload-ref-tests' (a two-article history
; opened through the host's open; the rows hold handles 0 and 1), and the
; arena is the open's: the two payloads sealed in history order.  The owner
; is that Store in its first position (fn-own-store is the car).
(in-package "ACL2")
(include-book "../../books/owner-feed-article")
(include-book "acceptance-payload-ref-tests")
(include-book "must-fail-checked")

(defconst *ofa-t-o* (cons *apr-t-s* nil))
(defconst *ofa-t-msgid-1* (fn-record-string-octets "<apr-1@example.invalid>"))
(defconst *ofa-t-msgid-9* (fn-record-string-octets "<apr-9@example.invalid>"))

(defun ofa-t-arena (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((fn-arena (fn-arena-seal-list '(72 105 13 10) fn-arena)))
    (fn-arena-seal-list '(89 111 13 10) fn-arena)))

; The subject over the open's arena.
(defun ofa-t-article (o msgid)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let ((fn-arena (ofa-t-arena fn-arena)))
        (mv (fn-ofa-feed-article o msgid fn-arena) fn-arena))
      r)))

; The keystone's right side, executably: fn-ofa-wire-feed-article's body (a
; defun-nx) over the same arena.
(defun ofa-t-wire (o msgid)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let ((fn-arena (ofa-t-arena fn-arena)))
        (mv (let ((a (fn-find-article
                      (fn-record-octets-string msgid)
                      (fn-articles-wire-of
                       (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store o))))
                       fn-arena))))
              (if (consp a) (fn-article-payload a) nil))
            fn-arena))
      r)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-ofa-feed-article-is-the-feed-article-over-alpha.
; Positive: the antecedent holds, and both sides are the article's bytes.
(assert-event (fn-apr-store-at-restp (fn-own-store *ofa-t-o*)))
(assert-event (equal (ofa-t-article *ofa-t-o* *ofa-t-msgid-1*) '(89 111 13 10)))
(assert-event (equal (ofa-t-article *ofa-t-o* *ofa-t-msgid-1*)
                     (ofa-t-wire *ofa-t-o* *ofa-t-msgid-1*)))
; An absent Message-ID: no bytes on either side.
(assert-event (equal (ofa-t-article *ofa-t-o* *ofa-t-msgid-9*) nil))
(assert-event (equal (ofa-t-wire *ofa-t-o* *ofa-t-msgid-9*) nil))
; The defect this replaces: the payload position the host handed the port
; before the fix is the HANDLE, not the bytes.
(assert-event (equal (fn-apr-feed-article *ofa-t-o* *ofa-t-msgid-1*) 1))
(assert-event (not (equal (fn-apr-feed-article *ofa-t-o* *ofa-t-msgid-1*)
                          (ofa-t-wire *ofa-t-o* *ofa-t-msgid-1*))))

; Hypothesis removal: fn-apr-store-at-restp.  The same Store with its event
; index emptied (acceptance-payload-ref-tests' *apr-t-unindexed*): the
; omitted hypothesis fails and so does the conclusion (the index finds no
; row; the acceptance field still holds the article).
(defconst *ofa-t-unindexed* (cons *apr-t-unindexed* nil))
(assert-event (not (fn-apr-store-at-restp (fn-own-store *ofa-t-unindexed*))))
(assert-event (equal (ofa-t-article *ofa-t-unindexed* *ofa-t-msgid-1*) nil))
(assert-event (equal (ofa-t-wire *ofa-t-unindexed* *ofa-t-msgid-1*) '(89 111 13 10)))
(assert-event (not (equal (ofa-t-article *ofa-t-unindexed* *ofa-t-msgid-1*)
                          (ofa-t-wire *ofa-t-unindexed* *ofa-t-msgid-1*))))

;  KEYSTONE fn-ofa-feed-article-is-the-owner-step-article (PKT-EG-2b): the
; book owner's step reads the handle's bytes, the host's article.
(defun ofa-t-model (o msgid)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let ((fn-arena (ofa-t-arena fn-arena)))
        (mv (fn-handle-bytes (fn-own-feed-article o msgid) fn-arena) fn-arena))
      r)))
(assert-event (fn-apr-store-at-restp (fn-own-store *ofa-t-o*)))
(assert-event (equal (ofa-t-model *ofa-t-o* *ofa-t-msgid-1*) '(89 111 13 10)))
(assert-event (equal (ofa-t-article *ofa-t-o* *ofa-t-msgid-1*)
                     (ofa-t-model *ofa-t-o* *ofa-t-msgid-1*)))
; Mutation (the defect): the model handing the HANDLE is not the host's bytes.
(must-fail-checked (assert-event (equal (ofa-t-article *ofa-t-o* *ofa-t-msgid-1*)
                                        (fn-own-feed-article *ofa-t-o* *ofa-t-msgid-1*))))
; Hypothesis removal (fn-apr-store-at-restp): the unindexed Store; the host
; finds no row, the model's acceptance field still names handle 1.
(assert-event (not (fn-apr-store-at-restp (fn-own-store *ofa-t-unindexed*))))
(assert-event (not (equal (ofa-t-article *ofa-t-unindexed* *ofa-t-msgid-1*)
                          (ofa-t-model *ofa-t-unindexed* *ofa-t-msgid-1*))))

; fn-ofa-feed-article-is-an-octet-list: the witness arena is an arena
; (fn-arena-p) and the bytes are octets; the handle is not.
(assert-event (fn-cbor-octet-listp (ofa-t-article *ofa-t-o* *ofa-t-msgid-1*)))
(assert-event (not (fn-cbor-octet-listp (fn-apr-feed-article *ofa-t-o* *ofa-t-msgid-1*))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-ofa-publication-command-words-have-octets.
; The feed port's publication of a 335's send, rendered by the host-called
; renderer (fn-ores-feed-port-publication): the command is the IHAVE
; article, handed to the port as the bytes (after the fix) or as the handle
; (before it).
(defun ofa-t-send-pub (article)
  (declare (xargs :verify-guards nil))
  (fn-ores-feed-port-publication :send nil
                                 (list (cons "peer" (list (list :command 3 article))))
                                 nil nil))

(defconst *ofa-t-good* (ofa-t-send-pub '(89 111 13 10)))
(defconst *ofa-t-handle* (ofa-t-send-pub 1))
(defconst *ofa-t-none* (ofa-t-send-pub nil))

; Positive: the bytes render (the dot-terminated block) and the publication
; passes unchanged as :send with octets.
(assert-event (fn-ores-feed-publication-p *ofa-t-good*))
(assert-event (equal (fn-ores-feedpub-status *ofa-t-good*) :ok))
(assert-event (equal (fn-ofa-publication *ofa-t-good*) *ofa-t-good*))
(assert-event (equal (fn-ores-feedpub-word (fn-ofa-publication *ofa-t-good*)) :send))
(assert-event (consp (fn-ores-feedpub-command (fn-ofa-publication *ofa-t-good*))))

; The pre-fix publication: :send with an EMPTY command, the renderer's status
; naming its refusal -- what the host stopped the owner on.
(assert-event (fn-ores-feed-publication-p *ofa-t-handle*))
(assert-event (equal (fn-ores-feedpub-word *ofa-t-handle*) :send))
(assert-event (null (fn-ores-feedpub-command *ofa-t-handle*)))
(assert-event (not (equal (fn-ores-feedpub-status *ofa-t-handle*) :ok)))
; ... becomes :unsendable, keeps its plan, and its line names the reason.
(assert-event (equal (fn-ores-feedpub-word (fn-ofa-publication *ofa-t-handle*))
                     :unsendable))
(assert-event (equal (fn-ores-feedpub-plan (fn-ofa-publication *ofa-t-handle*))
                     (fn-ores-feedpub-plan *ofa-t-handle*)))
(assert-event (fn-ores-feed-publication-p (fn-ofa-publication *ofa-t-handle*)))
(assert-event (consp (fn-ores-feedpub-log-line (fn-ofa-publication *ofa-t-handle*))))
; An absent article (a nil command, status :ok) is :unsendable as :no-article.
(assert-event (equal (fn-ores-feedpub-status *ofa-t-none*) :ok))
(assert-event (null (fn-ores-feedpub-command *ofa-t-none*)))
(assert-event (equal (fn-ores-feedpub-word (fn-ofa-publication *ofa-t-none*))
                     :unsendable))
(assert-event (equal (fn-ofa-reason (fn-ores-feedpub-status *ofa-t-none*)) :no-article))

; fn-ofa-publication-is-well-formed, hypothesis removal: a value that is not
; a publication stays one that is not (the conclusion fails with the
; hypothesis).
(assert-event (not (fn-ores-feed-publication-p '(:feed-publication :quiet))))
(assert-event (not (fn-ores-feed-publication-p
                    (fn-ofa-publication '(:feed-publication :quiet)))))
