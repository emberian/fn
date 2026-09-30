# D25 virtual source inverse cursor

Status: runtime source and fixed-state component proofs; general inverse and
actual captured-confirmation/native composition remain open.

`fn-psc-begin(mode,n,msgid,agent-span,incoming-n)` creates a fixed 24-slot
cursor. Modes are `:agent`, `:source-incoming` and `:source-held`. The two
lengths come from the captured core provider and incoming octet buffer;
Message-ID is the retained core string. The agent is `(:agent start end)` in
the incoming source. Missing agent denotes the empty span, matching NIL in
the old inverse. The one incoming agent governs both source inverses.

`fn-psc-demand` returns `(:incoming offset)`, `(:held offset)`, `:control` or
`:none`. `fn-psc-step(cursor,byte)` consumes one demand or one fixed control
transition. The enclosing kernel must pay each transition from its supplied
quantum and obtain bytes under its exact captured token, lease and prefix.
The parser does not authenticate a host-supplied byte. Span comparison reads
one expected incoming-agent or source-date byte and one target byte in
separate steps. It retains scalar offsets and one cached byte; it never
materializes a header, article, agent, date or Message-ID octet list.

`fn-psc-result` returns `:pending`, `:no-source`, `(:agent start end)` or
`(:source K A B)`. The descriptor means source[K..A) followed by source[B..N).
In agent mode `:no-source` denotes NIL agent. In inverse mode it denotes the
old inverse's NIL, causing the enclosing comparison to use exact whole
payload equality. Hash equality is not a substitute for that comparison.

The compatibility target is `fn-pb-path-agent` and `fn-pbb-source-index`,
with `fn-record-string-octets(msgid)` used only in the logical abstraction.
It preserves generated Cancel-Lock then Cancel-Key skip, Path precedence
then block-agent fallback, optional v1/v2 stamp/Message-ID/Date/info recipes,
parameter lines, ambiguous v1 fallback and case-insensitive v3 Path unsplice.
Ground tests cover these cases, but do not establish the general inverse.

There is no stored-data ceiling here. Scheduling fuel belongs to the caller;
exhaustion retains a pending cursor. General carried demand bounds, exact
refinement, per-step physical allocation, source lease preservation and the
actual live host path remain obligations under PRF-1145 and SCN-1051.

The proof-only companion now carries exact residuals for the actual byte
comparison, `fn-pb-line` endpoint and `fn-inj-param-rest` result. Their
resumable micro-runs preserve these values and finish with fuel derived
from the remaining source or comparison extent. These are component
lemmas; the full agent span and source descriptor inverse remains open.
The reference leaves retain the old actual `fn-pb-*` and `fn-pbb-*` names
and unchanged event forms below the Store verdict wrappers.

The v3 Path finder now carries its source-relative scan result through
failed field probes and split CR/LF steps. Its strict rank decreases on
every actual byte/control transition, and its terminating logical trace
is proved equal to the actual paid step trace and `fn-pbb-path-scan`.
This closes the discovery component, before agent insertion comparison;
the full agent/source inverse and physical caller obligations remain open.

The v3 descriptor component now composes that finder with the actual
incoming-agent span comparison and literal bang check. It returns exactly
`fn-pbb-unsplice-at`, including empty-agent success and malformed refusal,
and is equated to an exact charged actual byte/control trace. The complete
agent discovery and v1/v2 recipe graph remain open.

The leading generated uppercase Path component now returns exactly the agent of `fn-pb-path-line-agent`, through an incoming span, and its finite proof completion equals the actual charged byte/control trace. Malformed tail recognition returns to the block comparison. Protected confined replay pc16 admitted the source and literal positive, malformed and source-extent hypothesis-removal witnesses. This is a component coordinate; complete block fallback, Cancel-Lock/Key composition, v1/v2 source inverse and native resource/lease composition remain open.

The retained Message-ID comparison now matches the actual caller denotation `fn-record-string-octets` and the existing generated Message-ID line strip, through its field, string and CRLF stages. Its completion equals the actual paid cursor trace. Protected confined replay pc17 admitted the six source leaves and complete literal reachable positive, malformed-tail and source-extent-removal checks. These are proof-only stage summaries; the served runtime retains its string and consumes one demanded byte/control transition per step. Complete Date/Info block, Lock/Key and source-inverse composition remain open.

The Injection-Info component now returns exactly the existing `fn-pb-info-line-agent` through incoming spans, including plain lines, first-semicolon parameters, empty agents and malformed fallback. Its completion equals the actual paid byte/control trace. Fresh confined pc18 replay admitted seven source leaves plus reachable full literal witnesses and the source-extent removal witness (39.12 seconds, 22,025,731 prover steps). Runtime remains unchanged. Complete optional Date/stamp block, Lock/Key, v1/v2 inverse, token/lease/funding and native composed confirmation remain open.

The full optional agent block now matches `fn-pb-block-agent`: fixed stamp49 and Date39 skips, retained Message-ID, and Injection-Info plain/parameter/malformed branches return exact incoming agent spans. Its completion equals the actual paid cursor trace. Fresh confined pc20 replay admitted eight source leaves and full reachable optional/Info-only/malformed/short-stamp/wrong-Message-ID witnesses plus the extent removal (81.04 seconds, 24,101,816 steps). The complete Lock/Key and Path precedence agent, v1/v2 inverses and token/lease/funding/native confirmation remain open. Runtime is unchanged.

The Cancel-Lock/Key skip now agrees exactly with `fn-pbb-skip-at` for either incoming or held virtual source, and its full completion equals the actual paid byte/control trace. Protected proper-local pc21 replay passed nine source leaves and five complete literal incoming/held/empty/malformed witnesses; an additional extent-removal witness passed in the same confined world. Whole Path/block agent precedence, v1/v2 source inverse and token, lease, funding and native composition remain open. Runtime57f is unchanged.

The complete incoming agent cursor now follows Cancel-Lock/Key skip, prefers the leading generated Path agent, and otherwise uses the optional block parser. Its returned span denotes exactly `fn-pb-path-agent` with the actual retained Message-ID denotation `fn-record-string-octets`, and its completion equals the actual charged byte/control trace. Protected proper-local pc22 replay passed ten leaves and complete literal Path precedence, Lock/Key, optional block, malformed, empty and source-extent-removal witnesses. Valid returned span bounds, v1/v2 source-index inverse and demand-token, lease, allocation, funding and native composition remain open. Runtime57f is unchanged.

The actual `fn-psc-begin :agent` entry with core-derived incoming length now completes to `:no-source` or `(:agent S E)` with natural bounds `S <= E <= N`. The span still denotes exactly the current `fn-pb-path-agent` result, and completion remains the actual paid cursor trace. Protected proper-local pc26 replay passed eleven leaves and complete agent literals. The source-resume suffix is factored unchanged into a separate leaf, preserving the certified fixed-shape invariant bytes. The v1/v2 source-index inverse, demand/token mapping, physical leases, allocation/funding and native join remain open.

The source Injection-Info inverse now matches the existing `fn-pbb-strip-info-at` for incoming or held virtual bytes, using the same retained incoming agent span. Its plain CRLF, semicolon parameter, empty agent, malformed and EOF branches return the exact scalar success offset or refusal; its full completion equals the actual paid cursor trace. Fresh proper-local pc27 replay passed eleven source leaves and six complete positive/malformed literals plus the extent-removal witness (83.44 seconds, 29,713,410 steps; the new source Info leaf alone 10.91 seconds, 3,014,543 steps). This proof-only component preserves runtime57f and certified invariantc2ea bytes. Full v1/v2 Stamp/Date/Message-ID ambiguity and source-index inverse, demand/token mapping, physical leases, allocation/funding and native joined confirmation remain open.

The captured 31-byte Date wrapper now matches the existing `fn-pbb-strip-at` of `fn-inj-date-line` on incoming or held virtual source, and its completion equals the actual paid cursor trace. Fresh proper-local pc29 replay passed twelve source leaves and seven rootforms (75.78 seconds, 32,909,064 steps), including complete incoming/held/malformed/EOF literals and a captured-span-bound removal witness. Runtime57f and certified invariantc2ea bytes remain unchanged. Full Stamp/v1/v2 source-index inverse, demand/token mapping, physical leases, allocation/funding and native confirmation remain open.

The source Info completion also preserves its selected virtual source configuration, retained Message-ID, incoming agent span and captured-date metadata, and returns the supplied continuation on every control result. The exact context predicates are extracted unchanged into a small refinement-only leaf. Fresh proper-local pc32 replay passed twelve leaves and eight rootforms (71.39 seconds, 30,404,211 steps), including strengthened full literals. An explicit paid-trace hint exposes the context metadata after extraction. Full source-index and native/resource composition remain open.

The complete after-Stamp recipe now matches `fn-pbb-source-after-stamp`: an Info-first v1 result is rejected when followed by the retained Message-ID or captured Date wrapper; otherwise the optional Message-ID and Date v2 recipe strips the same incoming agent's Info line. Initial Info EOF is proved to have a matched Info prefix, which excludes both optional field prefixes and preserves refusal. The recipe equals its actual paid byte/control trace. Fresh pc34 replay confined fourteen source leaves and passed twelve complete incoming/held, ambiguity, optional-field, parameter, empty-agent, malformed and EOF literals (82.05 seconds, 37,434,523 steps); a semantic captured-span-bound removal also passed. Paid-trace hypothesis minimality remains open. This proof-only checkpoint does not establish Stamp/leading-Path geometry, the complete source-index descriptor, actual source begin/result, token/lease/funding or native joined confirmation. Runtime and certified fixed-state bytes remain unchanged.

The Stamp geometry component equates the old copied, clamped date wrapper with the runtime fixed 31-byte skip and CRLF comparison, including short tails. Successful comparison establishes the carried date bound used by both same-agent recipe inverses. Fresh proper-local pc35 replay confined fifteen source leaves (133.43 seconds, 37,483,008 steps) and passed complete, short, malformed CRLF, EOF, incoming and held literals; the date-capture equality removal passed separately. This is a proof-only prerequisite to the full after-Path/source-index join, which remains open, along with actual begin/result, lease, funding and native confirmation.

The complete after-Path inverse now matches current `fn-pbb-source-after-path` and its actual paid cursor trace across Info-only, malformed Stamp and valid Stamp into the v1/v2 recipes. Fresh proper-local pc36 confined sixteen source leaves (162.07 seconds, 38,167,049 steps), with fourteen complete incoming/held, optional-field, ambiguity, parameter, malformed, EOF and empty-agent literals. An extent-hypothesis removal demonstrates a changed semantic result while affirming both retained hypotheses; paid-trace hypothesis minimality remains open. Runtime and certified fixed-state bytes are unchanged. The leading Path/skip/v3 wrapper, universal begin/result legal terminal descriptor, token/lease/funding and actual native confirmation remain open.

The generated leading Path prefix now matches current `fn-pbb-strip-at(fn-inj-path-line(agent),position,source)` using the same retained incoming agent span in either mode. Field, agent and suffix failures reset to the original skip position; success carries the exact Path flag into the Stamp recipe. The named prefix completion also equals actual paid byte/control steps. Fresh proper-local pc38 confines eighteen source leaves (108.79 seconds, 39,404,969 steps), with seven complete prefix literals, affirmative skip/natural-position hypothesis removal, and both recipe flag values. The universal source-index begin/terminal descriptor, actual native captured-controller installation and resource/lease/lifetime proofs remain open.

The actual source begin boundary now composes Cancel-Lock/Key skip, the generated leading Path comparison, complete v1/v2 recipes and v3 unsplice. For either incoming or held mode, core-derived lengths and a legal incoming agent span, `fn-psc-source-begin-paid-completion-is-current-buffer-source-index` equates the actual paid cursor run with current `fn-pbb-source-index` on the same incoming agent, retained Message-ID and selected virtual source. Completion is `:done`, with `:no-source` or a legal `(:source K A B)` where `0 <= K <= A <= B <= N`. The logical completion and cost are proof-only summaries; the runtime still consumes one demanded byte or control transition. Fresh proper-local pc39 admitted twenty source leaves and twelve complete recipe/malformed literals. The initial load and literal attempts used 250.18 ACL2 seconds and 39,757,909 steps; the corrected Cancel-Lock/Key literal and remaining cases, including four affirmative length/span hypothesis removals, used another 3,009 steps. Runtime57f and certified fixed-state c2ea bytes are unchanged. Remaining hypothesis minimality, actual native controller installation/SAME, allowance/allocation/funding, physical demanded-byte authority and all-alias lifetime remain open. No normal certificate, image or deployment claim transfers from this source admission.
