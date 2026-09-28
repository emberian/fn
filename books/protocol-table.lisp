; fn's NNTP protocol table: one row per command (lane defprotocol, G4 of
; planning/extrapolation-2026-09-27.md section 3).
;
; Five hand-kept copies of one table lived apart: the dispatcher's arms, the
; RFC citations of specs/nntp-audit.md, the accepted/refused/uncertain
; reading of each reply, the fuzzer's grammar (tests/fuzz_nntp.py) and the
; FAQ's command list.  This book is the table they are read from.  It is
; data and the `defprotocol' macro that checks it; it includes nothing, so
; it can sit under the nntp cluster.  What the table claims of the
; dispatcher is proved in books/protocol-codes.lisp: every reply code
; fn-nntp-command-pinned emits for a command is in that command's row.
;
; Nothing here is read by evaluating a book: tools/protocol_emit.py reads the
; `defprotocol' form with the ledger's non-evaluating reader and writes the
; JSON the fuzzer and tools/docs_check.py read.
;
; A ROW is (NAME . PLIST), NAME the command keyword as RFC 3977 section 3.1
; spells it (the dispatcher compares case-insensitively: fn-nntp-keywordp),
; or a parenthesized name for a pseudo-row no keyword can equal.  The PLIST:
;
;   :rfc       the section that defines the command, as a string.
;   :dispatch  the layer whose dispatcher recognizes the command:
;              :session / :archive / :pinned (fn-nntp-command-pinned's
;              three arms), :auth (fn-auth-command, books/nntp-auth.lisp),
;              :peer (fn-peer-command, books/peer-inbound.lisp), or a
;              pseudo-row's :syntax / :unrecognized / :connection.
;   :parser    the EXISTING functions that decide the arguments' grammar
;              (names, never rewritten here).
;   :model     the function the reference arm calls; :cat the catalog
;              arm's (books/served-catalog.lisp fn-nntp-archive-command-cat,
;              the served one once sca-join-5 lands); :xref the Xref arm's
;              (books/nntp-xref.lisp, books/nntp-reader-compat.lisp).
;   :framing   :command, or :article when the reply hands the connection to
;              article mode (POST's 340).  A pinned connection may be sent
;              only :command replies unsolicited: books/nntp-auth-fold.lisp's
;              fn-auth-fold-command-pinned-offers-only-post is this column
;              (books/protocol-codes.lisp derives its case split from it).
;   :replies   the replies the command may receive, each
;              (CODE CLASS LAYER KEY TEXT . FLAGS):
;                CODE   the three-digit status (RFC 3977 section 3.2);
;                CLASS  :accepted, :refused or :uncertain (AGENTS.md: the
;                       three stay distinct at every boundary);
;                LAYER  the dispatcher that sends it: :reader
;                       (fn-nntp-command-pinned), :auth, :peer, :post
;                       (fn-nntp-post-step), :owner (the owner's completion
;                       or admission, books/owner-*.lisp), :connection;
;                KEY    the situation, unique within the row;
;                TEXT   the line; with FLAG :computed a template whose
;                       upper-case words are values;
;                FLAGS  :computed, and :unreachable for a defensive branch
;                       no composed path reaches (named where the source
;                       says so; it keeps the code in the row because the
;                       theorem is unconditional).
;   :fuzz      the arguments tests/fuzz_nntp.py sends after the command
;              word, in its generator's language (read by the fuzzer through
;              tools/protocol_emit.py, never by ACL2): a string is a word;
;              (:pool P) a word from the fuzzer's pool P; (:choice W...) one
;              of the words; (:opt PROB W...) the words with that
;              probability; (:msgid) an identifier; (:pool+msgid P) a word of
;              P or a fresh identifier; (:alt SEQ...) one of the sequences;
;              (:split (BOUND W...)...) the first sequence whose BOUND
;              exceeds one uniform draw; (:bound NAME I) the Ith part of a
;              value the step drew first; (:rep S N) S repeated N times;
;              (:rep-choice (W...) N) one word repeated a draw below N
;              times; (:cases CMDS...) the command lists a step indexes.
;   :faq       one line for the operator FAQ's command list.
;
; LIST's second keyword is a :variants column: (KEYWORD RFC-SECTION).

(in-package "ACL2")

(defun fn-proto-classp (x)
  (declare (xargs :guard t))
  (or (equal x :accepted) (equal x :refused) (equal x :uncertain)))

(defun fn-proto-layerp (x)
  (declare (xargs :guard t))
  (or (equal x :reader) (equal x :auth) (equal x :peer) (equal x :post)
      (equal x :owner) (equal x :connection)))

(defun fn-proto-flagsp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (or (equal (car x) :computed) (equal (car x) :unreachable))
           (fn-proto-flagsp (cdr x)))
    (null x)))

; A reply entry.  The code's class is not free: 1xx, 2xx and 3xx are
; accepted (3xx: the command may continue); 4xx and 5xx are refused unless
; the entry says the outcome is uncertain.  A 2xx or 3xx is never refused
; or uncertain.
(defun fn-proto-replyp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (<= 5 (len x))
       (natp (car x)) (<= 100 (car x)) (< (car x) 600)
       (fn-proto-classp (cadr x))
       (if (< (car x) 400)
           (equal (cadr x) :accepted)
         (not (equal (cadr x) :accepted)))
       (fn-proto-layerp (caddr x))
       (keywordp (cadddr x))
       (stringp (car (cddddr x)))
       (<= 3 (length (car (cddddr x))))
       ;; The text begins with the code: "NNN" then SP or the end.
       (equal (take 3 (coerce (car (cddddr x)) 'list))
              (explode-atom (car x) 10))
       (or (equal (length (car (cddddr x))) 3)
           (equal (char (car (cddddr x)) 3) #\Space))
       (fn-proto-flagsp (cdr (cddddr x)))))

(defun fn-proto-reply-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (fn-proto-replyp (car x)) (fn-proto-reply-listp (cdr x)))
    (null x)))

(defun fn-proto-keys (replies)
  (declare (xargs :guard (fn-proto-reply-listp replies)))
  (if (consp replies)
      (cons (cadddr (car replies)) (fn-proto-keys (cdr replies)))
    nil))

(defun fn-proto-plist-get (key plist)
  (declare (xargs :guard t))
  (if (and (consp plist) (consp (cdr plist)))
      (if (equal (car plist) key)
          (cadr plist)
        (fn-proto-plist-get key (cddr plist)))
    nil))

(defun fn-proto-symbol-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (symbolp (car x)) (car x) (fn-proto-symbol-listp (cdr x)))
    (null x)))

(defun fn-proto-dispatchp (x)
  (declare (xargs :guard t))
  (member-equal x '(:session :archive :pinned :auth :peer
                    :syntax :unrecognized :connection)))

(defun fn-proto-rowp (row)
  (declare (xargs :guard t))
  (and (consp row)
       (stringp (car row))
       (true-listp (cdr row))
       (let ((plist (cdr row)))
         (and (stringp (fn-proto-plist-get :rfc plist))
              (fn-proto-dispatchp (fn-proto-plist-get :dispatch plist))
              (fn-proto-symbol-listp (fn-proto-plist-get :parser plist))
              (fn-proto-symbol-listp (fn-proto-plist-get :model plist))
              (fn-proto-symbol-listp (fn-proto-plist-get :cat plist))
              (fn-proto-symbol-listp (fn-proto-plist-get :xref plist))
              (member-equal (fn-proto-plist-get :framing plist)
                            '(:command :article))
              (fn-proto-reply-listp (fn-proto-plist-get :replies plist))
              (no-duplicatesp-equal
               (fn-proto-keys (fn-proto-plist-get :replies plist)))
              (stringp (fn-proto-plist-get :faq plist))))))

(defun fn-proto-names (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (cons (if (consp (car rows)) (car (car rows)) nil)
            (fn-proto-names (cdr rows)))
    nil))

(defun fn-proto-rows-okp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-proto-rowp (car rows)) (fn-proto-rows-okp (cdr rows)))
    (null rows)))

(defun fn-proto-tablep (rows)
  (declare (xargs :guard t))
  (and (fn-proto-rows-okp rows)
       (no-duplicatesp-equal (fn-proto-names rows))))

; The codes a row's replies carry at LAYER, without repeats, in order.
(defun fn-proto-layer-codes (replies layer acc)
  (declare (xargs :guard (and (fn-proto-reply-listp replies) (true-listp acc))))
  (if (consp replies)
      (fn-proto-layer-codes
       (cdr replies) layer
       (if (and (equal (caddr (car replies)) layer)
                (not (member-equal (car (car replies)) acc)))
           (append acc (list (car (car replies))))
         acc))
    acc))

(defun fn-proto-row-replies (row)
  (declare (xargs :guard t))
  (let ((replies (and (consp row) (fn-proto-plist-get :replies (cdr row)))))
    (if (fn-proto-reply-listp replies) replies nil)))

; ((NAME . CODES) ...): each row with a :reader reply, and its reader codes.
; A row with none (AUTHINFO, STARTTLS, XREDEEM) is not the reader
; dispatcher's: that dispatcher answers it as the unrecognized pseudo-row.
(defun fn-proto-reader-alist (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (let ((codes (fn-proto-layer-codes (fn-proto-row-replies (car rows)) :reader nil)))
        (if (and (consp (car rows)) (stringp (car (car rows))) (consp codes)
                 (not (member-equal (fn-proto-plist-get :dispatch (cdr (car rows)))
                                    '(:syntax :unrecognized :connection))))
            (cons (cons (car (car rows)) codes)
                  (fn-proto-reader-alist (cdr rows)))
          (fn-proto-reader-alist (cdr rows))))
    nil))

(defun fn-proto-row (name rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows)) (equal (car (car rows)) name))
          (car rows)
        (fn-proto-row name (cdr rows)))
    nil))

; The reader codes of the pseudo-row whose :dispatch is KIND.
(defun fn-proto-pseudo-codes (kind rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows))
               (equal (fn-proto-plist-get :dispatch (cdr (car rows))) kind))
          (fn-proto-layer-codes (fn-proto-row-replies (car rows)) :reader nil)
        (fn-proto-pseudo-codes kind (cdr rows)))
    nil))

; The rows whose :framing is :article.
(defun fn-proto-article-framing-names (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (and (consp (car rows))
               (equal (fn-proto-plist-get :framing (cdr (car rows))) :article))
          (cons (car (car rows)) (fn-proto-article-framing-names (cdr rows)))
        (fn-proto-article-framing-names (cdr rows)))
    nil))

(defun fn-proto-text-in (key replies)
  (declare (xargs :guard (fn-proto-reply-listp replies)))
  (if (consp replies)
      (if (and (equal (cadddr (car replies)) key)
               (not (member-equal :computed (cdr (cddddr (car replies))))))
          (car (cddddr (car replies)))
        (fn-proto-text-in key (cdr replies)))
    nil))

; A reply's text by (command, key): what a call site writes instead of the
; literal.  `fn-proto-text' is a MACRO, so the term a book admits is the
; literal itself and no proof or execution sees a lookup.
(defun fn-proto-text-of (name key rows)
  (declare (xargs :guard t))
  (let ((row (fn-proto-row name rows)))
    (fn-proto-text-in key (fn-proto-row-replies row))))

(defmacro defprotocol (name &rest rows)
  `(progn
     (defconst ,name ',rows)
     (assert-event (fn-proto-tablep ,name)
                   :msg "a protocol row is malformed (fn-proto-rowp)")
     (defconst *fn-proto-reader-alist* (fn-proto-reader-alist ,name))
     (defconst *fn-proto-syntax-codes* (fn-proto-pseudo-codes :syntax ,name))
     (defconst *fn-proto-unrecognized-codes*
       (fn-proto-pseudo-codes :unrecognized ,name))
     (defconst *fn-proto-article-framing* (fn-proto-article-framing-names ,name))
     (defmacro fn-proto-text (command key)
       (let ((text (fn-proto-text-of command key ,name)))
         (if (stringp text)
             text
           (er hard 'fn-proto-text
               "No literal reply ~x0 for ~x1 in the protocol table."
               key command))))))

; -----------------------------------------------------------------------------
; The table.  Rows in the order of RFC 3977 section 5 onward, then the
; extensions, then the pseudo-rows.  A reader row's :reader replies are the
; ones books/protocol-codes.lisp proves complete.

(defprotocol *fn-proto-table*

  ("CAPABILITIES"
   :rfc "RFC 3977 5.2" :dispatch :session
   :parser (fn-nntp-keyword-tokenp)
   :model (fn-nntp-capabilities) :cat nil :xref nil
   :framing :command
   :fuzz ((:opt 1/5 (:choice "x" "AUTOUPDATE")))
   :replies ((101 :accepted :reader :list "101 capability list follows")
             (501 :refused :reader :syntax "501 syntax error")
             (101 :accepted :auth :list-auth "101 capability list follows")
             (101 :accepted :peer :list-peer "101 capability list follows"))
   :faq "What this node offers you now, as a list of labels.")

  ("HELP"
   :rfc "RFC 3977 7.2" :dispatch :session
   :parser nil
   :model (fn-nntp-help) :cat nil :xref nil
   :framing :command
   :fuzz ()
   :replies ((100 :accepted :reader :text "100 help text follows")
             (501 :refused :reader :syntax "501 syntax error"))
   :faq "The commands this node answers, one per line.")

  ("MODE"
   :rfc "RFC 3977 5.3; RFC 4644 2.3 (MODE STREAM)" :dispatch :session
   :parser (fn-nntp-keywordp)
   :model (fn-nntp-mode-response) :cat nil :xref nil
   :framing :command
   :fuzz ((:choice "READER" "STREAM" "" "reader" "POSTER" "X"))
   :replies ((200 :accepted :reader :posting "200 posting allowed")
             (201 :accepted :reader :no-posting "201 posting prohibited")
             (502 :refused :reader :no-reader
                  "502 reading service permanently unavailable" :unreachable)
             (501 :refused :reader :syntax "501 syntax error")
             (203 :accepted :peer :streaming "203 streaming permitted"))
   :faq "MODE READER says whether you may post; peers use MODE STREAM.")

  ("QUIT"
   :rfc "RFC 3977 5.4" :dispatch :session
   :parser nil
   :model (fn-nntp-session-command) :cat nil :xref nil
   :framing :command
   :fuzz ()
   :replies ((205 :accepted :reader :closing "205 closing connection")
             (501 :refused :reader :syntax "501 syntax error"))
   :faq "Ends the connection.")

  ("GROUP"
   :rfc "RFC 3977 6.1.1" :dispatch :archive
   :parser (fn-nntp-printable-tokenp)
   :model (fn-nntp-group-result) :cat (fn-nntp-group-result-cat) :xref nil
   :framing :command
   :fuzz ((:pool :groups) (:opt 1/20 "x"))
   :replies ((211 :accepted :reader :selected "211 COUNT LOW HIGH GROUP" :computed)
             (411 :refused :reader :no-group "411 no such newsgroup")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Selects a group; answers its count and first and last numbers.")

  ("LISTGROUP"
   :rfc "RFC 3977 6.1.2" :dispatch :archive
   :parser (fn-nntp-printable-tokenp fn-nntp-parse-range)
   :model (fn-gidx-listgroup-command fn-nntp-listgroup-command)
   :cat (fn-nntp-listgroup-command-cat) :xref nil
   :framing :command
   :fuzz ((:opt 4/5 (:pool :groups) (:opt 1/2 (:pool :ranges))))
   :replies ((211 :accepted :reader :listed "211 COUNT LOW HIGH GROUP list follows" :computed)
             (411 :refused :reader :no-group "411 no such newsgroup")
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Selects a group and lists its article numbers, optionally a range.")

  ("LAST"
   :rfc "RFC 3977 6.1.3" :dispatch :archive
   :parser nil
   :model (fn-nntp-next-or-last) :cat nil :xref nil
   :framing :command
   :fuzz ()
   :replies ((223 :accepted :reader :moved "223 NUMBER MESSAGE-ID retrieved" :computed)
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (420 :refused :reader :no-current "420 no current article")
             (422 :refused :reader :no-previous "422 no previous article")
             (423 :refused :reader :reclaimed "423 article reclaimed")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-identifier
                  "503 stored article identifier unavailable" :unreachable)
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Moves to the previous article in the group.")

  ("NEXT"
   :rfc "RFC 3977 6.1.4" :dispatch :archive
   :parser nil
   :model (fn-nntp-next-or-last) :cat nil :xref nil
   :framing :command
   :fuzz ()
   :replies ((223 :accepted :reader :moved "223 NUMBER MESSAGE-ID retrieved" :computed)
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (420 :refused :reader :no-current "420 no current article")
             (421 :refused :reader :no-next "421 no next article")
             (423 :refused :reader :reclaimed "423 article reclaimed")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-identifier
                  "503 stored article identifier unavailable" :unreachable)
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Moves to the next article in the group.")

  ("ARTICLE"
   :rfc "RFC 3977 6.2.1" :dispatch :archive
   :parser (fn-nntp-number-tokenp fn-nntp-message-id-tokenp)
   :model (fn-nntp-retrieval fn-nntp-msgid-retrieval-indexed fn-nntp-withdrawn-reply)
   :cat (fn-nntp-number-retrieval-cat fn-nntp-msgid-retrieval-cat) :xref (fn-rcompat-retrieval)
   :framing :command
   :fuzz ((:split (2/5 (:msgid)) (4/5 (:pool :ranges))))
   :replies ((220 :accepted :reader :sent "220 NUMBER MESSAGE-ID article follows" :computed)
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (420 :refused :reader :no-current "420 no current article")
             (423 :refused :reader :no-number "423 no article with that number")
             (423 :refused :reader :reclaimed-number "423 article reclaimed")
             (423 :refused :reader :withdrawn-number "423 withdrawn")
             (430 :refused :reader :no-msgid "430 no article with that message-id")
             (430 :refused :reader :reclaimed-msgid "430 article reclaimed")
             (430 :refused :reader :withdrawn-msgid "430 withdrawn")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-framing "503 stored article framing unavailable")
             (503 :refused :reader :no-identifier
                  "503 stored article identifier unavailable" :unreachable)
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Sends a whole article, by number, by Message-ID, or the current one.")

  ("HEAD"
   :rfc "RFC 3977 6.2.2" :dispatch :archive
   :parser (fn-nntp-number-tokenp fn-nntp-message-id-tokenp)
   :model (fn-nntp-retrieval fn-nntp-msgid-retrieval-indexed fn-nntp-withdrawn-reply)
   :cat (fn-nntp-number-retrieval-cat fn-nntp-msgid-retrieval-cat) :xref (fn-rcompat-retrieval)
   :framing :command
   :fuzz ((:split (2/5 (:msgid)) (4/5 (:pool :ranges))))
   :replies ((221 :accepted :reader :sent "221 NUMBER MESSAGE-ID headers follow" :computed)
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (420 :refused :reader :no-current "420 no current article")
             (423 :refused :reader :no-number "423 no article with that number")
             (423 :refused :reader :reclaimed-number "423 article reclaimed")
             (423 :refused :reader :withdrawn-number "423 withdrawn")
             (430 :refused :reader :no-msgid "430 no article with that message-id")
             (430 :refused :reader :reclaimed-msgid "430 article reclaimed")
             (430 :refused :reader :withdrawn-msgid "430 withdrawn")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-framing "503 stored article framing unavailable")
             (503 :refused :reader :no-identifier
                  "503 stored article identifier unavailable" :unreachable)
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Sends an article's header.")

  ("BODY"
   :rfc "RFC 3977 6.2.3" :dispatch :archive
   :parser (fn-nntp-number-tokenp fn-nntp-message-id-tokenp)
   :model (fn-nntp-retrieval fn-nntp-msgid-retrieval-indexed fn-nntp-withdrawn-reply)
   :cat (fn-nntp-number-retrieval-cat fn-nntp-msgid-retrieval-cat) :xref nil
   :framing :command
   :fuzz ((:split (2/5 (:msgid)) (4/5 (:pool :ranges))))
   :replies ((222 :accepted :reader :sent "222 NUMBER MESSAGE-ID body follows" :computed)
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (420 :refused :reader :no-current "420 no current article")
             (423 :refused :reader :no-number "423 no article with that number")
             (423 :refused :reader :reclaimed-number "423 article reclaimed")
             (423 :refused :reader :withdrawn-number "423 withdrawn")
             (430 :refused :reader :no-msgid "430 no article with that message-id")
             (430 :refused :reader :reclaimed-msgid "430 article reclaimed")
             (430 :refused :reader :withdrawn-msgid "430 withdrawn")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-framing "503 stored article framing unavailable")
             (503 :refused :reader :no-identifier
                  "503 stored article identifier unavailable" :unreachable)
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Sends an article's body.")

  ("STAT"
   :rfc "RFC 3977 6.2.4" :dispatch :archive
   :parser (fn-nntp-number-tokenp fn-nntp-message-id-tokenp)
   :model (fn-nntp-retrieval fn-nntp-msgid-retrieval-indexed fn-nntp-withdrawn-reply)
   :cat (fn-nntp-number-retrieval-cat fn-nntp-msgid-retrieval-cat) :xref nil
   :framing :command
   :fuzz ((:split (2/5 (:msgid)) (4/5 (:pool :ranges))))
   :replies ((223 :accepted :reader :sent "223 NUMBER MESSAGE-ID retrieved" :computed)
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (420 :refused :reader :no-current "420 no current article")
             (423 :refused :reader :no-number "423 no article with that number")
             (423 :refused :reader :reclaimed-number "423 article reclaimed")
             (423 :refused :reader :withdrawn-number "423 withdrawn")
             (430 :refused :reader :no-msgid "430 no article with that message-id")
             (430 :refused :reader :reclaimed-msgid "430 article reclaimed")
             (430 :refused :reader :withdrawn-msgid "430 withdrawn")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-identifier
                  "503 stored article identifier unavailable" :unreachable)
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Says whether an article exists, and moves to it by number.")

  ("OVER"
   :rfc "RFC 3977 8.3" :dispatch :archive
   :parser (fn-nntp-parse-range fn-nntp-message-id-tokenp)
   :model (fn-nntp-over-response fn-nntp-over-range-indexed)
   :cat (fn-nntp-over-range-cat) :xref (fn-nntp-xref-reply)
   :framing :command
   :fuzz ((:opt 4/5 (:pool+msgid :ranges)))
   :replies ((224 :accepted :reader :overview "224 overview information follows")
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (420 :refused :reader :no-current "420 no current article")
             (420 :refused :reader :none-selected "420 no article(s) selected")
             (423 :refused :reader :empty-range "423 no articles in that range")
             (423 :refused :reader :reclaimed-number "423 article reclaimed")
             (430 :refused :reader :no-msgid "430 no article with that message-id")
             (430 :refused :reader :reclaimed-msgid "430 article reclaimed")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-framing "503 stored article framing unavailable")
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Overview lines (subject, author, date, ids, size) for a range.")

  ("XOVER"
   :rfc "RFC 2980 2.8" :dispatch :archive
   :parser (fn-nntp-parse-range)
   :model (fn-nntp-xover-response fn-nntp-over-range-indexed)
   :cat (fn-nntp-over-range-cat) :xref (fn-nntp-xref-reply)
   :framing :command
   :fuzz ((:opt 4/5 (:pool+msgid :ranges)))
   :replies ((224 :accepted :reader :overview "224 overview information follows")
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (420 :refused :reader :no-current "420 no current article")
             (420 :refused :reader :none-selected "420 no article(s) selected")
             (423 :refused :reader :empty-range "423 no articles in that range")
             (423 :refused :reader :reclaimed-number "423 article reclaimed")
             (430 :refused :reader :no-msgid "430 no article with that message-id")
             (430 :refused :reader :reclaimed-msgid "430 article reclaimed")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-framing "503 stored article framing unavailable")
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "OVER's older spelling.")

  ("HDR"
   :rfc "RFC 3977 8.5" :dispatch :archive
   :parser (fn-nntp-parse-range fn-nntp-message-id-tokenp)
   :model (fn-nntp-hdr-response fn-nntp-verdict-hdr-response
           fn-nntp-control-hdr-response fn-nntp-enrollment-hdr-response)
   :cat (fn-nntp-hdr-command-cat) :xref (fn-nntp-xref-reply fn-rcompat-hdr)
   :framing :command
   :fuzz ((:pool :header-fields) (:opt 7/10 (:pool+msgid :ranges)))
   :replies ((225 :accepted :reader :headers "225 headers follow")
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (420 :refused :reader :no-current "420 no current article")
             (420 :refused :reader :none-selected "420 no article(s) selected")
             (423 :refused :reader :empty-range "423 no articles in that range")
             (423 :refused :reader :reclaimed-number "423 article reclaimed")
             (430 :refused :reader :no-msgid "430 no article with that message-id")
             (430 :refused :reader :reclaimed-msgid "430 article reclaimed")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-framing "503 stored article framing unavailable")
             (503 :refused :reader :no-control-status "503 control status unavailable")
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "One header field for a range; also :fn-verified, :fn-control and :fn-enrollment.")

  ("XHDR"
   :rfc "RFC 2980 2.6" :dispatch :archive
   :parser (fn-nntp-parse-range fn-nntp-message-id-tokenp)
   :model (fn-nntp-xhdr-response) :cat (fn-nntp-hdr-command-cat)
   :xref (fn-nntp-xref-reply fn-rcompat-hdr)
   :framing :command
   :fuzz ((:pool :header-fields) (:opt 7/10 (:pool+msgid :ranges)))
   :replies ((221 :accepted :reader :header "221 header follows")
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (420 :refused :reader :no-current "420 no current article")
             (420 :refused :reader :none-selected "420 no article(s) selected")
             (423 :refused :reader :empty-range "423 no articles in that range")
             (423 :refused :reader :reclaimed-number "423 article reclaimed")
             (430 :refused :reader :no-msgid "430 no article with that message-id")
             (430 :refused :reader :reclaimed-msgid "430 article reclaimed")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-framing "503 stored article framing unavailable")
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "HDR's older spelling.")

  ("XPAT"
   :rfc "RFC 2980 2.9" :dispatch :archive
   :parser (fn-nntp-parse-range fn-nntp-message-id-tokenp fn-wildmat-parse)
   :model (fn-nntp-xpat-response) :cat (fn-nntp-xpat-response-cat) :xref nil
   :framing :command
   :fuzz ((:pool :header-names) (:pool+msgid :ranges) (:pool :wildmats))
   :replies ((221 :accepted :reader :header "221 header follows")
             (412 :refused :reader :no-group-selected "412 no newsgroup selected")
             (430 :refused :reader :no-msgid "430 no article with that message-id")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-framing "503 stored article framing unavailable")
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "XHDR filtered by a wildmat on the field's content.")

  ("LIST"
   :rfc "RFC 3977 7.6; RFC 6048" :dispatch :archive
   :parser (fn-nntp-keyword-tokenp fn-wildmat-parse)
   :model (fn-nntp-list-command fn-gidx-list-counts-command)
   :cat (fn-nntp-list-counts-command-cat) :xref (fn-nntp-xref-reply fn-rcompat-reply)
   :framing :command
   :fuzz ((:alt ()
               ("ACTIVE" (:opt 1/2 (:pool :wildmats)))
               ("NEWSGROUPS" (:opt 1/2 (:pool :wildmats)))
               ("OVERVIEW.FMT" (:opt 1/2 (:pool :wildmats)))
               ("HEADERS" (:opt 1/2 (:pool :wildmats)))
               ("ACTIVE.TIMES" (:opt 1/2 (:pool :wildmats)))
               ("DISTRIB.PATS" (:opt 1/2 (:pool :wildmats)))
               ("MOTD" (:opt 1/2 (:pool :wildmats)))
               ("COUNTS" (:opt 1/2 (:pool :wildmats)))
               ("SUBSCRIPTIONS" (:opt 1/2 (:pool :wildmats)))
               ("HEADERS MSGID" (:opt 1/2 (:pool :wildmats)))
               ("HEADERS RANGE" (:opt 1/2 (:pool :wildmats)))
               ("X" (:opt 1/2 (:pool :wildmats)))))
   :variants (("ACTIVE" "RFC 3977 7.6.3") ("ACTIVE.TIMES" "RFC 3977 7.6.4")
              ("COUNTS" "RFC 6048 2.2") ("DISTRIB.PATS" "RFC 3977 7.6.5")
              ("DISTRIBUTIONS" "RFC 6048 2.3") ("HEADERS" "RFC 3977 8.6")
              ("MOTD" "RFC 6048 2.5") ("NEWSGROUPS" "RFC 3977 7.6.6")
              ("OVERVIEW.FMT" "RFC 3977 8.4") ("SUBSCRIPTIONS" "RFC 6048 2.6"))
   :replies ((215 :accepted :reader :active "215 list of active newsgroups follows")
             (215 :accepted :reader :newsgroups "215 list of newsgroups follows")
             (215 :accepted :reader :times "215 information follows")
             (215 :accepted :reader :motd "215 message of the day follows")
             (215 :accepted :reader :overview-fmt "215 order of fields in overview database")
             (215 :accepted :reader :headers "215 field list follows")
             (215 :accepted :reader :subscriptions "215 list of recommended newsgroups follows")
             (501 :refused :reader :syntax "501 syntax error")
             (501 :refused :reader :variant "501 unsupported LIST variant")
             (503 :refused :reader :not-stored "503 data item not stored")
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Lists groups and server data; the second word names which.")

  ("NEWGROUPS"
   :rfc "RFC 3977 7.3" :dispatch :archive
   :parser (fn-nntp-newgroups-date-parse fn-nntp-newgroups-time-parse)
   :model (fn-nntp-newgroups-response) :cat nil :xref (fn-rcompat-reply)
   :framing :command
   :fuzz ((:bound :date 0) (:bound :date 1) (:opt 2/5 (:choice "GMT" "UTC" "gmt" "X")))
   :replies ((231 :accepted :reader :listed "231 list of new newsgroups follows")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-century "503 two-digit year needs a wall clock reading")
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Groups created since a date and time (UTC).")

  ("NEWNEWS"
   :rfc "RFC 3977 7.4" :dispatch :archive
   :parser (fn-wildmat-parse fn-nntp-newgroups-date-parse fn-nntp-newgroups-time-parse)
   :model (fn-nntp-newnews-response) :cat nil :xref nil
   :framing :command
   :fuzz ((:pool :wildmats) (:bound :date 0) (:bound :date 1) (:opt 2/5 (:choice "GMT" "UTC" "gmt" "X")))
   :replies ((230 :accepted :reader :listed "230 list of new articles by message-id follows")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-century "503 two-digit year needs a wall clock reading")
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "Message-IDs of articles accepted since a date, in matching groups.")

  ("DATE"
   :rfc "RFC 3977 7.1" :dispatch :session
   :parser nil
   :model (fn-nntp-date-response) :cat nil :xref nil
   :framing :command
   :fuzz ()
   :replies ((111 :accepted :reader :date "111 YYYYMMDDhhmmss" :computed)
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :no-observation "503 no clock observation supplied")
             (503 :refused :reader :no-wall "503 server holds no wall clock reading")
             (503 :refused :reader :out-of-range "503 clock reading outside the representable range"))
   :faq "The node's clock, in UTC.")

  ("POST"
   :rfc "RFC 3977 6.3.1; RFC 5537 3.5" :dispatch :session
   :parser nil
   :model (fn-nntp-post-offer fn-nntp-post-step) :cat nil :xref nil
   :framing :article
   :fuzz ((:opt 1/20 "x"))
   :replies ((340 :accepted :reader :send "340 send article to be posted")
             (501 :refused :reader :syntax "501 syntax error")
             (480 :refused :auth :auth-required "480 authentication required")
             (440 :refused :auth :principal "440 posting not permitted for this principal")
             (440 :refused :post :not-permitted "440 posting not permitted")
             (441 :refused :post :refused "441 posting failed; REASON" :computed)
             (441 :refused :post :not-received "441 posting failed; the article was not received")
             (403 :uncertain :post :malformed-session
                  "403 internal fault; the posting session is malformed")
             (240 :accepted :owner :received "240 article received OK")
             (240 :accepted :owner :key-change-refused
                  "240 article received OK; the key change it carries was refused (key-change-refused)")
             (441 :uncertain :owner :uncertain "441 posting failed; the outcome is uncertain, do not repost")
             (440 :refused :owner :shedding "440 posting not permitted now; REASON" :computed)
             (441 :refused :owner :shed "441 posting failed; REASON" :computed))
   :faq "Sends an article; 340 asks for it, 240 means it is stored.")

  ("IHAVE"
   :rfc "RFC 3977 6.3.2" :dispatch :peer
   :parser (fn-nntp-message-id-tokenp)
   :model (fn-peer-command) :cat nil :xref nil
   :framing :command
   :fuzz ((:bound :mid 0))
   :replies ((502 :refused :reader :transit "502 transit is not permitted on this connection")
             (335 :accepted :peer :send "335 send it; end with <CR-LF>.<CR-LF>")
             (435 :refused :peer :duplicate "435 duplicate")
             (435 :refused :peer :not-wanted "435 not wanted; REASON" :computed)
             (436 :refused :peer :retry "436 retry later; REASON" :computed)
             (235 :accepted :peer :transferred "235 article transferred OK")
             (436 :uncertain :peer :uncertain "436 transfer failed; the outcome is uncertain")
             (436 :refused :peer :not-received "436 transfer failed; the article was not received")
             (436 :refused :peer :closing "436 the article was not received; closing")
             (437 :refused :peer :rejected "437 transfer rejected; REASON" :computed)
             (501 :refused :peer :syntax "501 syntax error"))
   :faq "A peer offers an article by Message-ID (peers only).")

  ("CHECK"
   :rfc "RFC 4644 2.3" :dispatch :peer
   :parser (fn-nntp-message-id-tokenp)
   :model (fn-peer-command) :cat nil :xref nil
   :framing :command
   :fuzz ((:msgid))
   :replies ((502 :refused :reader :transit "502 transit is not permitted on this connection")
             (238 :accepted :peer :wanted "238 MESSAGE-ID" :computed)
             (431 :refused :peer :later "431 MESSAGE-ID" :computed)
             (438 :refused :peer :not-wanted "438 MESSAGE-ID" :computed)
             (501 :refused :peer :syntax "501 syntax error"))
   :faq "A streaming peer asks whether an article is wanted (peers only).")

  ("TAKETHIS"
   :rfc "RFC 4644 2.4" :dispatch :peer
   :parser (fn-nntp-message-id-tokenp)
   :model (fn-peer-command) :cat nil :xref nil
   :framing :command
   :fuzz ((:bound :mid 0))
   :replies ((502 :refused :reader :transit "502 transit is not permitted on this connection")
             (239 :accepted :peer :transferred "239 MESSAGE-ID" :computed)
             (439 :refused :peer :rejected "439 MESSAGE-ID" :computed)
             (436 :refused :peer :retry "436 MESSAGE-ID" :computed)
             (501 :refused :peer :syntax "501 syntax error"))
   :faq "A streaming peer sends an article (peers only).")

  ("AUTHINFO"
   :rfc "RFC 4643 2.3" :dispatch :auth
   :parser (fn-auth-token-argp)
   :model (fn-auth-authinfo) :cat nil :xref nil
   :framing :command
   :fuzz ((:cases (("USER" (:choice "fuzz" "nobody" "" (:rep "u" 600)))
                   ("PASS" (:choice "fuzz-password" "wrong" "" (:rep "p" 600))))
                  (("PASS" "fuzz-password"))
                  (("SASL" (:choice "PLAIN" "PLAIN AGZ1enoAZnV6ei1wYXNzd29yZA==" "X")))
                  (((:choice "GENERIC" "SIMPLE" "" "user")))
                  (("USER" "fuzz"))))
   :replies ((381 :accepted :auth :password "381 password required")
             (281 :accepted :auth :accepted "281 authentication accepted")
             (481 :refused :auth :failed "481 authentication failed")
             (482 :refused :auth :sequence "482 authentication commands issued out of sequence")
             (483 :refused :auth :protect "483 a protected channel is required; use STARTTLS")
             (501 :refused :auth :syntax "501 syntax error")
             (502 :refused :auth :already "502 already authenticated")
             (502 :refused :auth :no-sasl "502 no SASL mechanism is offered"))
   :faq "Logs in: AUTHINFO USER name, then AUTHINFO PASS password.")

  ("STARTTLS"
   :rfc "RFC 4642 2.2" :dispatch :auth
   :parser nil
   :model (fn-auth-starttls) :cat nil :xref nil
   :framing :command
   :fuzz ()
   :replies ((382 :accepted :auth :continue "382 continue with TLS negotiation")
             (501 :refused :auth :syntax "501 syntax error")
             (502 :refused :auth :active "502 a TLS layer is already active")
             (580 :refused :auth :cannot "580 can not initiate TLS negotiation"))
   :faq "Turns on TLS on this connection before you log in.")

  ("XREDEEM"
   :rfc "fn (PRF-164)" :dispatch :auth
   :parser (fn-auth-token-argp)
   :model (fn-auth-xredeem fn-auth-redeem-outcome) :cat nil :xref nil
   :framing :command
   :fuzz ((:rep-choice ("code" "" (:rep "x" 600)) 3))
   :replies ((381 :accepted :auth :password "381 send the password with XREDEEM PASS")
             (281 :accepted :auth :bound
                  "281 account bound; authenticate with AUTHINFO on a new connection")
             (482 :refused :auth :refused "482 invitation code refused")
             (482 :refused :auth :sequence "482 redemption commands issued out of sequence")
             (483 :refused :auth :protect "483 a protected channel is required; use STARTTLS")
             (501 :refused :auth :syntax "501 syntax error")
             (502 :refused :auth :already "502 already authenticated"))
   :faq "Redeems an invitation code for a login.")

  ("XFNCATCHUP"
   :rfc "fn (PRF-325, NNT-053)" :dispatch :pinned
   :parser (fn-cu-parse-request)
   :model (fn-cu-serve-reply) :cat nil :xref nil
   :framing :command
   :fuzz ((:pool :wildmats) (:pool :ranges) (:choice "0" "x") (:pool :ranges))
   :replies ((291 :accepted :reader :batch "291 NEXT END done|more CHAIN" :computed)
             (423 :refused :reader :past-end "423 catch-up position past the end of the log")
             (501 :refused :reader :syntax "501 syntax error")
             (503 :refused :reader :out-of-range "503 catch-up log position out of range")
             (503 :refused :reader :no-projection "503 archive projection unavailable")
             (480 :refused :auth :auth-required "480 authentication required"))
   :faq "A peer's batched catch-up over the articles it may read (peers only).")

  ("(syntax)"
   :rfc "RFC 3977 3.2.1" :dispatch :syntax
   :parser (fn-nntp-command-inputp fn-nntp-tokenize fn-nntp-keyword-tokenp
            fn-nntp-command-arguments-at-mostp)
   :model (fn-nntp-command-pinned) :cat nil :xref nil
   :framing :command
   :replies ((501 :refused :reader :syntax "501 syntax error"))
   :faq "A line that is not a command: 501.")

  ("(unrecognized)"
   :rfc "RFC 3977 3.2.1" :dispatch :unrecognized
   :parser nil
   :model (fn-nntp-session-command) :cat nil :xref nil
   :framing :command
   :replies ((500 :refused :reader :unknown "500 command not recognized"))
   :faq "A command this node does not know: 500.")

  ("(connection)"
   :rfc "RFC 3977 5.1" :dispatch :connection
   :parser nil
   :model (fn-served-greeting fn-exp-admit) :cat nil :xref nil
   :framing :command
   :replies ((200 :accepted :connection :greeting-posting "200 fn-nntp experimental server ready")
             (201 :accepted :connection :greeting "201 fn-nntp experimental reader ready")
             (400 :refused :connection :busy "400 too many connections; try again later")
             (400 :refused :connection :busy-address
                  "400 too many connections from this address; try again later")
             (400 :refused :connection :auth-failures-address
                  "400 too many authentication failures from this address; try again later")
             (400 :refused :connection :auth-failures
                  "400 too many authentication failures; closing connection")
             (403 :uncertain :connection :fault
                  "403 internal fault; this connection is closed and the server continues"))
   :faq "What the node says on connect, or when it cannot take you."))
