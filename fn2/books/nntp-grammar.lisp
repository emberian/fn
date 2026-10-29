;; The NNTP command and reply grammar (layer-D brief item 2; D2a), declared
;; through DEFGRAMMAR. Provenance: the keywords, HELP rows and citations are
;; H's spec-derived model (fn2/tests/model/nntp_model.py: HELP, KEYWORDS,
;; SPECS); the reply rows are fn1's served table (books/protocol-table.lisp),
;; lifted once and polished (XFNCATCHUP's "done|more" reply is two replies);
;; the argument forms follow the model's validators and RFC 3977 section 3.1.
;; COMPRESS is admitted only after authentication (NNT-054; layer H's ruling
;; of 2026-10-29). tests/grammar-oracle.py checks this table against the model.
(in-package "ACL2")
(include-book "grammar")
(fn2-book-layer :d)

(defgrammar fn2-nntp
  ;; RFC 3977 section 3.1: 512 octets with CRLF, arguments at most 497;
  ;; RFC 5322 section 2.1.1: a block line of 998 octets plus CRLF.
  :line-cap 512 :args-cap 497 :block-line-cap 1000
  :states (:reader :peer :authenticated)
  :layers ((:reader nil) (:auth nil) (:post nil) (:owner nil) (:connection nil) (:peer :peer))
  :fields (("NUMBER" :number) ("COUNT" :number) ("LOW" :number) ("HIGH" :number) ("N" :number)
           ("CLEN" :number) ("NEXT" :number) ("END" :number) ("YYYYMMDDhhmmss" :digits14)
           ("MESSAGE-ID" :span) ("GROUP" :span) ("REASON" :span) ("CHALLENGE" :span)
           ("DIGEST" :span) ("CHAIN" :span))
  :general (
   (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
   (:unknown :code 500 :class :refused :layer :reader :text "500 command not recognized")
   (:greeting-posting :code 200 :class :accepted :layer :connection :text "200 fn-nntp experimental server ready")
   (:greeting :code 201 :class :accepted :layer :connection :text "201 fn-nntp experimental reader ready")
   (:busy :code 400 :class :refused :layer :connection :text "400 too many connections; try again later")
   (:busy-address :code 400 :class :refused :layer :connection :text "400 too many connections from this address; try again later")
   (:auth-failures-address :code 400 :class :refused :layer :connection :text "400 too many authentication failures from this address; try again later")
   (:auth-failures :code 400 :class :refused :layer :connection :text "400 too many authentication failures; closing connection")
   (:fault :code 403 :class :uncertain :layer :connection :text "403 internal fault; this connection is closed and the server continues"))
  :commands (
  (capabilities :keyword "CAPABILITIES"
   :spec "specs/nntp.md:3-23,1698-1736,2480-2507; RFC 3977 section 5.2"
   :args ((:opt :label)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 0
   :replies (
     (:list :code 101 :class :accepted :layer :reader :text "101 capability list follows")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:list-auth :code 101 :class :accepted :layer :auth :text "101 capability list follows")
     (:list-peer :code 101 :class :accepted :layer :peer :text "101 capability list follows")))
  (help :keyword "HELP"
   :spec "specs/nntp.md:51-93; RFC 3977 section 7.2"
   :args () :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 0
   :replies (
     (:text :code 100 :class :accepted :layer :reader :text "100 help text follows")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")))
  (quit :keyword "QUIT"
   :spec "specs/nntp.md:521-528; RFC 3977 section 5.4"
   :args () :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 0
   :replies (
     (:closing :code 205 :class :accepted :layer :reader :text "205 closing connection")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")))
  (mode :keyword "MODE"
   :spec "specs/nntp.md:14-24,2412-2443; RFC 3977 section 5.3"
   :args ((:keyword "READER" "STREAM")) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 0
   :replies (
     (:posting :code 200 :class :accepted :layer :reader :text "200 posting allowed")
     (:no-posting :code 201 :class :accepted :layer :reader :text "201 posting prohibited")
     (:no-reader :code 502 :class :refused :layer :reader :text "502 reading service permanently unavailable")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:streaming :code 203 :class :accepted :layer :peer :text "203 streaming permitted")))
  (date :keyword "DATE"
   :spec "specs/nntp.md:106-134; RFC 3977 section 7.1"
   :args () :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 0
   :replies (
     (:date :code 111 :class :accepted :layer :reader :text "111 YYYYMMDDhhmmss")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-observation :code 503 :class :refused :layer :reader :text "503 no clock observation supplied")
     (:no-wall :code 503 :class :refused :layer :reader :text "503 server holds no wall clock reading")
     (:out-of-range :code 503 :class :refused :layer :reader :text "503 clock reading outside the representable range")))
  (post :keyword "POST"
   :spec "specs/nntp.md:709-1480,1985-2010; RFC 3977 section 6.3.1"
   :args () :states (:reader :peer) :state-refusal nil
   :block (:after 340) :hand-off nil :help 0
   :replies (
     (:send :code 340 :class :accepted :layer :reader :text "340 send article to be posted")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")
     (:principal :code 440 :class :refused :layer :auth :text "440 posting not permitted for this principal")
     (:not-permitted :code 440 :class :refused :layer :post :text "440 posting not permitted")
     (:refused :code 441 :class :refused :layer :post :text "441 posting failed; REASON")
     (:refused-unparsable :code 441 :class :refused :layer :post :text "441 posting failed; the article is not valid syntax")
     (:refused-line-length :code 441 :class :refused :layer :post :text "441 posting failed; a header line is longer than 998 octets (RFC 5322 section 2.1.1); fold it")
     (:refused-header-fields-limit :code 441 :class :refused :layer :post :text "441 posting failed; the header has more fields than the profile's max-header-fields")
     (:refused-header-lines-limit :code 441 :class :refused :layer :post :text "441 posting failed; the header has more lines than the profile's max-header-lines")
     (:refused-header-octets-limit :code 441 :class :refused :layer :post :text "441 posting failed; the header has more octets than the profile's max-header-octets")
     (:refused-group-read-only :code 441 :class :refused :layer :post :text "441 posting failed; a group this article names is read-only here (LIST ACTIVE status n)")
     (:refused-approval-not-moderator :code 441 :class :refused :layer :post :text "441 posting failed; Approved is accepted only from a moderator of each moderated group named (LIST ACTIVE status m)")
     (:refused-moderation-unavailable :code 441 :class :refused :layer :post :text "441 posting failed; a moderated group is named and the article could not be forwarded to its moderation queue")
     (:refused-injection-info :code 441 :class :refused :layer :post :text "441 posting failed; Injection-Info must not be supplied")
     (:refused-xref :code 441 :class :refused :layer :post :text "441 posting failed; Xref must not be supplied")
     (:refused-injection-date-present :code 441 :class :refused :layer :post :text "441 posting failed; Injection-Date must not be supplied")
     (:refused-path-present :code 441 :class :refused :layer :post :text "441 posting failed; Path must not be supplied")
     (:refused-path-malformed :code 441 :class :refused :layer :post :text "441 posting failed; Path is not a valid path")
     (:refused-path-duplicate :code 441 :class :refused :layer :post :text "441 posting failed; Path appears more than once")
     (:refused-path-posted :code 441 :class :refused :layer :post :text "441 posting failed; Path must not carry a POSTED diagnostic")
     (:refused-newsgroups-missing :code 441 :class :refused :layer :post :text "441 posting failed; Newsgroups is required")
     (:refused-newsgroups-duplicate :code 441 :class :refused :layer :post :text "441 posting failed; Newsgroups appears more than once")
     (:refused-newsgroups-invalid :code 441 :class :refused :layer :post :text "441 posting failed; Newsgroups is not a valid newsgroup list")
     (:refused-message-id-duplicate :code 441 :class :refused :layer :post :text "441 posting failed; Message-ID appears more than once")
     (:refused-message-id-invalid :code 441 :class :refused :layer :post :text "441 posting failed; Message-ID is not a valid identifier")
     (:refused-from-missing :code 441 :class :refused :layer :post :text "441 posting failed; From is required")
     (:refused-from-duplicate :code 441 :class :refused :layer :post :text "441 posting failed; From appears more than once")
     (:refused-from-invalid :code 441 :class :refused :layer :post :text "441 posting failed; From is not a valid mailbox list")
     (:refused-subject-missing :code 441 :class :refused :layer :post :text "441 posting failed; Subject is required")
     (:refused-subject-duplicate :code 441 :class :refused :layer :post :text "441 posting failed; Subject appears more than once")
     (:refused-date-duplicate :code 441 :class :refused :layer :post :text "441 posting failed; Date appears more than once")
     (:refused-no-groups :code 441 :class :refused :layer :post :text "441 posting failed; no newsgroup was named")
     (:refused-unknown-group :code 441 :class :refused :layer :post :text "441 posting failed; a named newsgroup is not carried here")
     (:refused-oversize :code 441 :class :refused :layer :post :text "441 posting failed; the article exceeds the configured size")
     (:refused-clock-unusable :code 441 :class :refused :layer :post :text "441 posting failed; this server has no usable clock reading")
     (:refused-clock-out-of-range :code 441 :class :refused :layer :post :text "441 posting failed; this server clock is outside the modelled range")
     (:refused-posting-disallowed :code 441 :class :refused :layer :post :text "441 posting failed; posting is not permitted")
     (:refused-unnamed :code 441 :class :refused :layer :post :text "441 posting failed")
     (:not-received :code 441 :class :refused :layer :post :text "441 posting failed; the article was not received")
     (:malformed-session :code 403 :class :uncertain :layer :post :text "403 internal fault; the posting session is malformed")
     (:received :code 240 :class :accepted :layer :owner :text "240 article received OK")
     (:key-change-refused :code 240 :class :accepted :layer :owner :text "240 article received OK; the key change it carries was refused (key-change-refused)")
     (:uncertain :code 441 :class :uncertain :layer :owner :text "441 posting failed; the outcome is uncertain, do not repost")
     (:shedding :code 440 :class :refused :layer :owner :text "440 posting not permitted now; REASON")
     (:shed :code 441 :class :refused :layer :owner :text "441 posting failed; REASON")))
  (authinfo :keyword "AUTHINFO"
   :spec "specs/nntp.md:1482-1736; RFC 4643 sections 2.3,2.4"
   :args ((:keyword "USER" "PASS" "SASL") (:opt :token) (:opt :token)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 1
   :replies (
     (:password :code 381 :class :accepted :layer :auth :text "381 password required")
     (:accepted :code 281 :class :accepted :layer :auth :text "281 authentication accepted")
     (:failed :code 481 :class :refused :layer :auth :text "481 authentication failed")
     (:sequence :code 482 :class :refused :layer :auth :text "482 authentication commands issued out of sequence")
     (:protect :code 483 :class :refused :layer :auth :text "483 a protected channel is required; use STARTTLS")
     (:syntax :code 501 :class :refused :layer :auth :text "501 syntax error")
     (:already :code 502 :class :refused :layer :auth :text "502 already authenticated")
     (:sasl-continue :code 383 :class :accepted :layer :auth :text "383 CHALLENGE")
     (:sasl-accepted :code 283 :class :accepted :layer :auth :text "283 CHALLENGE")
     (:cancelled :code 481 :class :refused :layer :auth :text "481 authentication cancelled")
     (:no-mechanism :code 503 :class :refused :layer :auth :text "503 mechanism not recognized")
     (:base64 :code 504 :class :refused :layer :auth :text "504 base64 encoding error")))
  (starttls :keyword "STARTTLS"
   :spec "specs/nntp.md:1482-1509,1620-1696; RFC 4642 section 2.2"
   :args () :states (:reader :peer) :state-refusal nil
   :block nil :hand-off (:tls 382) :help 1
   :replies (
     (:continue :code 382 :class :accepted :layer :auth :text "382 continue with TLS negotiation")
     (:syntax :code 501 :class :refused :layer :auth :text "501 syntax error")
     (:active :code 502 :class :refused :layer :auth :text "502 a TLS layer is already active")
     (:cannot :code 580 :class :refused :layer :auth :text "580 can not initiate TLS negotiation")))
  (xredeem :keyword "XREDEEM"
   :spec "specs/nntp.md:1784-1914"
   :args (:token :token) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 1
   :replies (
     (:password :code 381 :class :accepted :layer :auth :text "381 send the password with XREDEEM PASS")
     (:bound :code 281 :class :accepted :layer :auth :text "281 account bound; authenticate with AUTHINFO on a new connection")
     (:refused :code 482 :class :refused :layer :auth :text "482 invitation code refused")
     (:sequence :code 482 :class :refused :layer :auth :text "482 redemption commands issued out of sequence")
     (:protect :code 483 :class :refused :layer :auth :text "483 a protected channel is required; use STARTTLS")
     (:syntax :code 501 :class :refused :layer :auth :text "501 syntax error")
     (:already :code 502 :class :refused :layer :auth :text "502 already authenticated")))
  (compress :keyword "COMPRESS"
   :spec "specs/nntp.md:2480-2536; RFC 8054 section 2.2"
   :args (:token) :states (:authenticated) :state-refusal :auth-required
   :block nil :hand-off (:compress 206) :help 1
   :replies (
     (:started :code 206 :class :accepted :layer :auth :text "206 compression active")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")
     (:syntax :code 501 :class :refused :layer :auth :text "501 syntax error")
     (:running :code 502 :class :refused :layer :auth :text "502 compression is already active")
     (:compressed :code 502 :class :refused :layer :auth :text "502 not permitted once a compression layer is active")
     (:algorithm :code 503 :class :refused :layer :auth :text "503 compression algorithm not supported")))
  (group :keyword "GROUP"
   :spec "specs/nntp.md:419-505; RFC 3977 section 6.1.1"
   :args (:token) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 2
   :replies (
     (:selected :code 211 :class :accepted :layer :reader :text "211 COUNT LOW HIGH GROUP")
     (:no-group :code 411 :class :refused :layer :reader :text "411 no such newsgroup")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (listgroup :keyword "LISTGROUP"
   :spec "specs/nntp.md:419-505; RFC 3977 section 6.1.2"
   :args ((:opt :token) (:opt :range)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 2
   :replies (
     (:listed :code 211 :class :accepted :layer :reader :text "211 COUNT LOW HIGH GROUP list follows")
     (:no-group :code 411 :class :refused :layer :reader :text "411 no such newsgroup")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (list :keyword "LIST"
   :spec "specs/nntp.md:182-235,364-416,1061-1118; RFC 3977 section 7.6; RFC 6048 section 2"
   :args ((:opt (:keyword "ACTIVE" "ACTIVE.TIMES" "COUNTS" "DISTRIB.PATS" "DISTRIBUTIONS" "HEADERS" "MOTD" "NEWSGROUPS" "OVERVIEW.FMT" "SUBSCRIPTIONS")) (:opt :token)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 2
   :replies (
     (:active :code 215 :class :accepted :layer :reader :text "215 list of active newsgroups follows")
     (:newsgroups :code 215 :class :accepted :layer :reader :text "215 list of newsgroups follows")
     (:times :code 215 :class :accepted :layer :reader :text "215 information follows")
     (:motd :code 215 :class :accepted :layer :reader :text "215 message of the day follows")
     (:overview-fmt :code 215 :class :accepted :layer :reader :text "215 order of fields in overview database")
     (:headers :code 215 :class :accepted :layer :reader :text "215 field list follows")
     (:subscriptions :code 215 :class :accepted :layer :reader :text "215 list of recommended newsgroups follows")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:variant :code 501 :class :refused :layer :reader :text "501 unsupported LIST variant")
     (:not-stored :code 503 :class :refused :layer :reader :text "503 data item not stored")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (next :keyword "NEXT"
   :spec "specs/nntp.md:419-505; RFC 3977 section 6.1.4"
   :args () :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 2
   :replies (
     (:moved :code 223 :class :accepted :layer :reader :text "223 NUMBER MESSAGE-ID retrieved")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:no-current :code 420 :class :refused :layer :reader :text "420 no current article")
     (:no-next :code 421 :class :refused :layer :reader :text "421 no next article")
     (:reclaimed :code 423 :class :refused :layer :reader :text "423 article reclaimed")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-identifier :code 503 :class :refused :layer :reader :text "503 stored article identifier unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (last :keyword "LAST"
   :spec "specs/nntp.md:419-505; RFC 3977 section 6.1.3"
   :args () :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 2
   :replies (
     (:moved :code 223 :class :accepted :layer :reader :text "223 NUMBER MESSAGE-ID retrieved")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:no-current :code 420 :class :refused :layer :reader :text "420 no current article")
     (:no-previous :code 422 :class :refused :layer :reader :text "422 no previous article")
     (:reclaimed :code 423 :class :refused :layer :reader :text "423 article reclaimed")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-identifier :code 503 :class :refused :layer :reader :text "503 stored article identifier unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (newgroups :keyword "NEWGROUPS"
   :spec "specs/nntp.md:106-134,375-389; RFC 3977 section 7.3"
   :args (:date :time (:opt :gmt)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 2
   :replies (
     (:listed :code 231 :class :accepted :layer :reader :text "231 list of new newsgroups follows")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-century :code 503 :class :refused :layer :reader :text "503 two-digit year needs a wall clock reading")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (newnews :keyword "NEWNEWS"
   :spec "specs/nntp.md:237-317; RFC 3977 section 7.4"
   :args (:wildmat :date :time (:opt :gmt)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 2
   :replies (
     (:listed :code 230 :class :accepted :layer :reader :text "230 list of new articles by message-id follows")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-century :code 503 :class :refused :layer :reader :text "503 two-digit year needs a wall clock reading")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (article :keyword "ARTICLE"
   :spec "specs/nntp.md:330-362,400-424,979-988; RFC 3977 section 6.2.1"
   :args ((:opt :ref)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 3
   :replies (
     (:sent :code 220 :class :accepted :layer :reader :text "220 NUMBER MESSAGE-ID article follows")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:no-current :code 420 :class :refused :layer :reader :text "420 no current article")
     (:no-number :code 423 :class :refused :layer :reader :text "423 no article with that number")
     (:reclaimed-number :code 423 :class :refused :layer :reader :text "423 article reclaimed")
     (:withdrawn-number :code 423 :class :refused :layer :reader :text "423 withdrawn")
     (:no-msgid :code 430 :class :refused :layer :reader :text "430 no article with that message-id")
     (:reclaimed-msgid :code 430 :class :refused :layer :reader :text "430 article reclaimed")
     (:withdrawn-msgid :code 430 :class :refused :layer :reader :text "430 withdrawn")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-framing :code 503 :class :refused :layer :reader :text "503 stored article framing unavailable")
     (:no-identifier :code 503 :class :refused :layer :reader :text "503 stored article identifier unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (head :keyword "HEAD"
   :spec "specs/nntp.md:400-424; RFC 3977 section 6.2.2"
   :args ((:opt :ref)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 3
   :replies (
     (:sent :code 221 :class :accepted :layer :reader :text "221 NUMBER MESSAGE-ID headers follow")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:no-current :code 420 :class :refused :layer :reader :text "420 no current article")
     (:no-number :code 423 :class :refused :layer :reader :text "423 no article with that number")
     (:reclaimed-number :code 423 :class :refused :layer :reader :text "423 article reclaimed")
     (:withdrawn-number :code 423 :class :refused :layer :reader :text "423 withdrawn")
     (:no-msgid :code 430 :class :refused :layer :reader :text "430 no article with that message-id")
     (:reclaimed-msgid :code 430 :class :refused :layer :reader :text "430 article reclaimed")
     (:withdrawn-msgid :code 430 :class :refused :layer :reader :text "430 withdrawn")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-framing :code 503 :class :refused :layer :reader :text "503 stored article framing unavailable")
     (:no-identifier :code 503 :class :refused :layer :reader :text "503 stored article identifier unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (body :keyword "BODY"
   :spec "specs/nntp.md:400-424; RFC 3977 section 6.2.3"
   :args ((:opt :ref)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 3
   :replies (
     (:sent :code 222 :class :accepted :layer :reader :text "222 NUMBER MESSAGE-ID body follows")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:no-current :code 420 :class :refused :layer :reader :text "420 no current article")
     (:no-number :code 423 :class :refused :layer :reader :text "423 no article with that number")
     (:reclaimed-number :code 423 :class :refused :layer :reader :text "423 article reclaimed")
     (:withdrawn-number :code 423 :class :refused :layer :reader :text "423 withdrawn")
     (:no-msgid :code 430 :class :refused :layer :reader :text "430 no article with that message-id")
     (:reclaimed-msgid :code 430 :class :refused :layer :reader :text "430 article reclaimed")
     (:withdrawn-msgid :code 430 :class :refused :layer :reader :text "430 withdrawn")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-framing :code 503 :class :refused :layer :reader :text "503 stored article framing unavailable")
     (:no-identifier :code 503 :class :refused :layer :reader :text "503 stored article identifier unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (stat :keyword "STAT"
   :spec "specs/nntp.md:419-424; RFC 3977 section 6.2.4"
   :args ((:opt :ref)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 3
   :replies (
     (:sent :code 223 :class :accepted :layer :reader :text "223 NUMBER MESSAGE-ID retrieved")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:no-current :code 420 :class :refused :layer :reader :text "420 no current article")
     (:no-number :code 423 :class :refused :layer :reader :text "423 no article with that number")
     (:reclaimed-number :code 423 :class :refused :layer :reader :text "423 article reclaimed")
     (:withdrawn-number :code 423 :class :refused :layer :reader :text "423 withdrawn")
     (:no-msgid :code 430 :class :refused :layer :reader :text "430 no article with that message-id")
     (:reclaimed-msgid :code 430 :class :refused :layer :reader :text "430 article reclaimed")
     (:withdrawn-msgid :code 430 :class :refused :layer :reader :text "430 withdrawn")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-identifier :code 503 :class :refused :layer :reader :text "503 stored article identifier unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (over :keyword "OVER"
   :spec "specs/nntp.md:319-362; RFC 3977 section 8.3"
   :args ((:opt :ref-range)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 4
   :replies (
     (:overview :code 224 :class :accepted :layer :reader :text "224 overview information follows")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:no-current :code 420 :class :refused :layer :reader :text "420 no current article")
     (:none-selected :code 420 :class :refused :layer :reader :text "420 no article(s) selected")
     (:empty-range :code 423 :class :refused :layer :reader :text "423 no articles in that range")
     (:reclaimed-number :code 423 :class :refused :layer :reader :text "423 article reclaimed")
     (:no-msgid :code 430 :class :refused :layer :reader :text "430 no article with that message-id")
     (:reclaimed-msgid :code 430 :class :refused :layer :reader :text "430 article reclaimed")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-framing :code 503 :class :refused :layer :reader :text "503 stored article framing unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (xover :keyword "XOVER"
   :spec "specs/nntp.md:136-159; RFC 2980 section 2.8"
   :args ((:opt :ref-range)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 4
   :replies (
     (:overview :code 224 :class :accepted :layer :reader :text "224 overview information follows")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:no-current :code 420 :class :refused :layer :reader :text "420 no current article")
     (:none-selected :code 420 :class :refused :layer :reader :text "420 no article(s) selected")
     (:empty-range :code 423 :class :refused :layer :reader :text "423 no articles in that range")
     (:reclaimed-number :code 423 :class :refused :layer :reader :text "423 article reclaimed")
     (:no-msgid :code 430 :class :refused :layer :reader :text "430 no article with that message-id")
     (:reclaimed-msgid :code 430 :class :refused :layer :reader :text "430 article reclaimed")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-framing :code 503 :class :refused :layer :reader :text "503 stored article framing unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (hdr :keyword "HDR"
   :spec "specs/nntp.md:400-416,2771-2806; RFC 3977 section 8.5"
   :args (:token (:opt :ref-range)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 4
   :replies (
     (:headers :code 225 :class :accepted :layer :reader :text "225 headers follow")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:no-current :code 420 :class :refused :layer :reader :text "420 no current article")
     (:none-selected :code 420 :class :refused :layer :reader :text "420 no article(s) selected")
     (:empty-range :code 423 :class :refused :layer :reader :text "423 no articles in that range")
     (:reclaimed-number :code 423 :class :refused :layer :reader :text "423 article reclaimed")
     (:no-msgid :code 430 :class :refused :layer :reader :text "430 no article with that message-id")
     (:reclaimed-msgid :code 430 :class :refused :layer :reader :text "430 article reclaimed")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-framing :code 503 :class :refused :layer :reader :text "503 stored article framing unavailable")
     (:no-control-status :code 503 :class :refused :layer :reader :text "503 control status unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (xhdr :keyword "XHDR"
   :spec "specs/nntp.md:136-159,400-416; RFC 2980 section 2.6"
   :args (:token (:opt :ref-range)) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 4
   :replies (
     (:header :code 221 :class :accepted :layer :reader :text "221 header follows")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:no-current :code 420 :class :refused :layer :reader :text "420 no current article")
     (:none-selected :code 420 :class :refused :layer :reader :text "420 no article(s) selected")
     (:empty-range :code 423 :class :refused :layer :reader :text "423 no articles in that range")
     (:reclaimed-number :code 423 :class :refused :layer :reader :text "423 article reclaimed")
     (:no-msgid :code 430 :class :refused :layer :reader :text "430 no article with that message-id")
     (:reclaimed-msgid :code 430 :class :refused :layer :reader :text "430 article reclaimed")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-framing :code 503 :class :refused :layer :reader :text "503 stored article framing unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (xpat :keyword "XPAT"
   :spec "specs/nntp.md:161-180,415-416; RFC 2980 section 2.9"
   :args (:token :ref-range :rest) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help 4
   :replies (
     (:header :code 221 :class :accepted :layer :reader :text "221 header follows")
     (:no-group-selected :code 412 :class :refused :layer :reader :text "412 no newsgroup selected")
     (:no-msgid :code 430 :class :refused :layer :reader :text "430 no article with that message-id")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-framing :code 503 :class :refused :layer :reader :text "503 stored article framing unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))
  (ihave :keyword "IHAVE"
   :spec "specs/nntp.md:530-537,2412-2443; RFC 3977 section 6.3.2"
   :args (:msgid) :states (:peer) :state-refusal :transit
   :block (:after 335) :hand-off nil :help 5
   :replies (
     (:transit :code 502 :class :refused :layer :reader :text "502 transit is not permitted on this connection")
     (:send :code 335 :class :accepted :layer :peer :text "335 send it; end with <CR-LF>.<CR-LF>")
     (:duplicate :code 435 :class :refused :layer :peer :text "435 duplicate")
     (:not-wanted :code 435 :class :refused :layer :peer :text "435 not wanted; REASON")
     (:retry :code 436 :class :refused :layer :peer :text "436 retry later; REASON")
     (:transferred :code 235 :class :accepted :layer :peer :text "235 article transferred OK")
     (:uncertain :code 436 :class :uncertain :layer :peer :text "436 transfer failed; the outcome is uncertain")
     (:not-received :code 436 :class :refused :layer :peer :text "436 transfer failed; the article was not received")
     (:closing :code 436 :class :refused :layer :peer :text "436 the article was not received; closing")
     (:rejected :code 437 :class :refused :layer :peer :text "437 transfer rejected; REASON")
     (:rejected-by-acceptance :code 437 :class :refused :layer :peer :text "437 transfer rejected; refused by acceptance")
     (:retry-no-clock :code 436 :class :refused :layer :peer :text "436 retry later; no usable clock reading")
     (:syntax :code 501 :class :refused :layer :peer :text "501 syntax error")))
  (check :keyword "CHECK"
   :spec "specs/nntp.md:2412-2443; RFC 4644 section 2.4"
   :args (:msgid) :states (:peer) :state-refusal :transit
   :block nil :hand-off nil :help 5
   :replies (
     (:transit :code 502 :class :refused :layer :reader :text "502 transit is not permitted on this connection")
     (:wanted :code 238 :class :accepted :layer :peer :text "238 MESSAGE-ID")
     (:later :code 431 :class :refused :layer :peer :text "431 MESSAGE-ID")
     (:not-wanted :code 438 :class :refused :layer :peer :text "438 MESSAGE-ID")
     (:syntax :code 501 :class :refused :layer :peer :text "501 syntax error")))
  (takethis :keyword "TAKETHIS"
   :spec "specs/nntp.md:530-537,2412-2443; RFC 4644 section 2.5"
   :args (:msgid) :states (:peer) :state-refusal :transit
   :block (:immediate) :hand-off nil :help 5
   :replies (
     (:transit :code 502 :class :refused :layer :reader :text "502 transit is not permitted on this connection")
     (:transferred :code 239 :class :accepted :layer :peer :text "239 MESSAGE-ID")
     (:rejected :code 439 :class :refused :layer :peer :text "439 MESSAGE-ID")
     (:retry :code 436 :class :refused :layer :peer :text "436 MESSAGE-ID")
     (:syntax :code 501 :class :refused :layer :peer :text "501 syntax error")))
  (xfncatchup :keyword "XFNCATCHUP"
   :spec "specs/nntp.md:676; RELEASE-PLAN section 1 NNTP: fn's own commands"
   :args (:wildmat :digits :token :number) :states (:peer) :state-refusal :transit
   :block nil :hand-off nil :help nil
   :replies (
     (:batch-done :code 291 :class :accepted :layer :reader :text "291 NEXT END done CHAIN")
     (:batch-more :code 291 :class :accepted :layer :reader :text "291 NEXT END more CHAIN")
     (:past-end :code 423 :class :refused :layer :reader :text "423 catch-up position past the end of the log")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:out-of-range :code 503 :class :refused :layer :reader :text "503 catch-up log position out of range")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")
     (:transit :code 502 :class :refused :layer :reader :text "502 transit is not permitted on this connection")))
  (xfn-zarticle :keyword "XFN-ZARTICLE"
   :spec "specs/nntp.md:2484-2499"
   :args (:msgid :rest) :states (:reader :peer) :state-refusal nil
   :block nil :hand-off nil :help nil
   :replies (
     (:stored :code 229 :class :accepted :layer :reader :text "229 DIGEST N CLEN stored payload follows")
     (:sent :code 220 :class :accepted :layer :reader :text "220 NUMBER MESSAGE-ID article follows")
     (:no-number :code 423 :class :refused :layer :reader :text "423 no article with that number")
     (:no-msgid :code 430 :class :refused :layer :reader :text "430 no article with that message-id")
     (:reclaimed-msgid :code 430 :class :refused :layer :reader :text "430 article reclaimed")
     (:withdrawn-msgid :code 430 :class :refused :layer :reader :text "430 withdrawn")
     (:syntax :code 501 :class :refused :layer :reader :text "501 syntax error")
     (:no-framing :code 503 :class :refused :layer :reader :text "503 stored article framing unavailable")
     (:no-identifier :code 503 :class :refused :layer :reader :text "503 stored article identifier unavailable")
     (:no-projection :code 503 :class :refused :layer :reader :text "503 archive projection unavailable")
     (:auth-required :code 480 :class :refused :layer :auth :text "480 authentication required")))))
