; fn: the runtime profile's limits, one table (G5, one profile source).
;
; Every figure below was written two to six times: in the book that uses it,
; in a host constant, in a launcher or build script, in a test and in the
; operator documentation.  Now each is one row here and everything else
; reads it:
;
;   * the books that reason with a figure define their constant from its row
;     (`fn-profile-limit', a macro that expands to the literal, so each
;     constant's value and every theorem about it are what they were);
;   * the raw host reads the books' constants (host/native/mux.lisp,
;     host/native/io.lisp), never a literal;
;   * the image build prints the SBCL runtime figures it saves into the
;     launcher (FN_NATIVE_TLS_LIMIT, FN_NATIVE_STACK_KIB: host/native/build.lisp),
;     and tools/build_native_host.sh writes those into the launcher;
;   * scripts, tests and documentation read this table through
;     tools/profile_limits.py, which reads this file without evaluating it
;     (so the table stays a literal: no computed row) and writes the
;     documentation's generated regions; `tools/profile_limits.py --check'
;     refuses a stale region and a known literal copy left behind.
;
; Each row is (KEY VALUE UNIT MEANING).  Changing a VALUE is a change to the
; supported profile: it recertifies the books that read it, and the
; documentation follows by regeneration, not by hand.
;
; The store profile's capacity fields (transactions, history, record and
; article sizes, groups, suffix) and their presets are
; books/byte-store-frame.lisp's (fn-bs-profile-preset) and heap-figure's; a
; store profile is the operator's, validated at init, not a runtime
; constant, so it is not a row here.
;
; No include-book, no rule, no function: a literal and a macro.

(in-package "ACL2")

(defconst *fn-profile-limits*
  '((:tls-limit 65536 "symbols"
     "SBCL's thread-local storage per thread (--tls-limit): the served world passed SBCL's default 16384 at load, so images build and run at this")
    (:stack-kib 1024 "KiB"
     "every thread's control stack (--control-stack-size), whatever the store profile")
    (:default-stack-kib 2048 "KiB"
     "the control stack when no store profile is named (help, --version): SBCL's own default")
    (:fixed-threads 12 "threads"
     "the node's threads that are not I/O loops or control clients")
    (:mux-loops 2 "threads"
     "the I/O loops every served connection is multiplexed on")
    (:control-clients 16 "clients"
     "concurrent control-socket clients the owner serves")
    (:thread-runtime-mib 4 "MiB"
     "SBCL's per-thread runtime beside its control stack (binding stack, alien stack, thread-local storage)")
    (:gc-nursery-mib 64 "MiB"
     "the collection trigger's cap: every dynamic space of 1 GiB or more collects after this much allocation")
    (:max-connections 32 "connections"
     "fn.toml's [server] max_connections when it names none")
    (:headroom-min-percent 10 "percent"
     "the [alerts] free-space headroom below which the operator is alerted")
    (:refusal-rate-per-minute 30 "refusals per minute"
     "the [alerts] refusal rate above which the operator is alerted")
    (:cooldown-seconds 900 "seconds"
     "the [alerts] quiet time between two alerts of one kind")
    (:exposure-per-address 8 "connections"
     "a public listener's connections held at once from one source address")
    (:exposure-steps-per-second 64 "steps per 1000 ms"
     "served steps one public address starts per quantum (one step: one host read)")
    (:exposure-first-seconds 60 "seconds"
     "a public connection's wait for its first command (RFC 3977 section 3.1 permits a shorter one)")
    (:exposure-idle-seconds 600 "seconds"
     "a public connection's autologout after that (RFC 3977 section 3.1: at least three minutes)")
    (:exposure-auth-failures 10 "per minute"
     "481 answers one public address may draw per minute")
    (:exposure-posts-per-minute 60 "per minute"
     "submissions per authenticated principal per minute on a public listener")))

; The row's VALUE, at macroexpansion: (fn-profile-limit :stack-kib) is the
; literal 1024 wherever it appears, and an unknown KEY is refused there.
(defmacro fn-profile-limit (key)
  (let ((row (assoc-eq key *fn-profile-limits*)))
    (if row
        (cadr row)
      (er hard 'fn-profile-limit "~x0 is not a row of *fn-profile-limits*." key))))
