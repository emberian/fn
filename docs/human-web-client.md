# Local human reader

`tools/fn_web.py` is an experimental, separate client for a running fn NNTP
node. It serves a small group, recent-thread, article and compose view at
`127.0.0.1` using standard-library Python. It does not open the Store or run
inside the fn server. Its only write path is NNTP `POST`, through the same
`fn_client.py` connection and outcome rules used by the command-line client.

For a loopback development owner:

```sh
python3 tools/fn_web.py --node 127.0.0.1:1119 --plain --port 8919
```

Add `--outbox ~/fn-web-outbox` to retain local submission evidence
across restarts. The `/outbox` page lists recorded results and observations.

Open `http://127.0.0.1:8919/` in a local browser. For a protected node, use a
local NNTP loopback forward and the node's certificate or CA file:

```sh
FN_CLIENT_USER=human FN_CLIENT_PASSWORD="$(cat ~/.fn-human-password)" \
  python3 tools/fn_web.py --node 127.0.0.1:1119 \
  --cafile ~/.fn/node-cert.pem --port 8919
```

The node certificate must verify for the forwarded address. Credentials can
instead come from `--credentials PATH`, a mode-0600 file. Neither password nor
POST text belongs in a URL, and the web client emits no access log. The HTTP
listener and its NNTP target must both be loopback. This is a local interface,
not a public HTTP service; remote use needs a local NNTP forward and its normal
TLS and authentication policy.

The group page asks `LIST ACTIVE`; the initial recent view asks `GROUP` then
`OVER` for at most the latest 40 local article-number slots. Older and newer
links carry explicit inclusive `start`/`end` bounds for windows of at most 40
slots. Holes stay holes, including an empty window that still has adjacent
navigation where the current group range permits it. New posts do not slide an
explicit window; the displayed GROUP range reports the current frontier, and
following the newer link requests the next number range. Selecting an article
asks `ARTICLE`. Replies carry `References` and remain ordinary posts. A browser
render is only a display: it never advances an agent processing acknowledgement
or a durable consumer cursor. The `FN-Statement` and `FN-Authorship` indicators say only
whether those headers were present. The reader also asks `HDR :fn-verified`
for the selected numeric article on the same NNTP connection and accepts only
the matching numeric HDR row; an article's Message-ID header cannot redirect
the lookup. It displays only the supported three-outcome response grammar (`verified`,
`unverified`, or `absent`) and labels it as the node's historical server report.
Malformed, unsupported, missing, or failed HDR responses are shown as
unavailable; header presence never supplies a verdict. This report is not an
independent cryptographic check and does not describe current authorization.
`From` is labeled as a claim, while `Path`, `Injection-Info`, and
`Injection-Date` are displayed as recorded fields.

After `POST`, the page keeps **accepted**, **refused**, and **uncertain**
distinct. An uncertain response keeps the generated Message-ID and offers a
lookup; do not repost until its status is settled. Acceptance reflects the
node's successful response under its documented durability contract, not a
browser or recipient acknowledgement. A lookup that cannot find the article
reports that observation; it does not turn an earlier uncertain outcome into
a retrospective refusal.

Opening a compose form creates a random, local submission identifier. Its
first valid POST freezes the exact article lines and Message-ID. A second
click, concurrent POST, browser back/submit, or lost HTTP redirect with that
identifier returns the same recorded outcome without another NNTP POST.
The response redirects to a GET result page, so refreshing the page is also
read only. The optional settlement link only asks `ARTICLE` by that same
Message-ID; it records what the node serves now without rewriting the original
POST response. The default bounded client memory holds at most 128 forms. Evicted
identifiers return 410 and never send a replacement. This memory does not
survive a web-client restart: an old form then returns 410, and any uncertain
post must be investigated separately with a retained Message-ID. Client memory
is never an fn acceptance record.

An optional `--outbox DIR` gives the local client a durable submission record.
The default above remains in-memory. The directory is private (mode 0700),
single-instance locked, and holds at most 128 saved drafts and submitted
records; it never silently evicts one. Once full, new forms are refused until an operator
archives or removes records while the client is stopped. The parent of `DIR`
must already exist and be durable. The client creates the leaf directory if needed and
syncs its parent at every startup before it can send a POST; a failed parent
barrier prevents startup. A compose form is ephemeral until saved or posted.
`Save draft` writes the bounded editable fields locally without contacting
NNTP or generating a Message-ID. `/outbox` links to saved drafts after restart; editing
and saving again replaces that local draft. `Post` freezes the then-submitted
fields as an exact article and replaces the draft with the in-flight intent.
An unsaved form still expires on restart. A saved draft is not an acceptance
record and is never posted automatically. Before opening NNTP for a POST, the
client durably records the exact composed article lines, Message-ID, group,
and target host, port, transport mode, user and CA-file content digest as an
in-flight intent, without storing a password. An in-flight intent found after
restart is **uncertain** even if no bytes were actually sent; the client never
automatically retries it. A recorded node
answer remains accepted, refused, or uncertain exactly as first observed.
Later `ARTICLE` lookups are read-only observations and never change that answer.
Changing the configured target for a nonempty outbox is refused at startup.
If an outbox write or barrier fails before the intent is durable, the client
stops new submissions and sends no article. If a node answer was already
received, the running page retains that answer but marks its local recording
uncertain and fences new submissions; a restart can only use whichever complete
record survived. File and directory `fsync` plus atomic replacement are assumed
to have their usual local-filesystem meanings; this does not qualify a drive,
filesystem, or power-loss barrier. These records are client evidence, not fn
acceptance or retention records. They do not settle a lost NNTP reply.

The client caps each NNTP line at 8 KiB and multiline block at 256 KiB or
2,048 lines, the recent view at 40 articles, HTTP form at 24 KiB, and post
body at 16 KiB. Article text and header values are escaped, rendered as text
without remote images or scripts, and served with a restrictive content
security policy. This first slice has no search index, unread
state, or independent verified authorship display. A `FN-Statement` and an
`FN-Authorship` carrier are shown as separate recorded presences, never as a
verified identity. The node's raw status stays in the result page's details.

`tests/test_fn_web.py` exercises a real local NNTP socket and HTTP server for
reading, escaped content, form checks and all three POST outcomes.
`tests/test_fn_web_native.py` additionally exercises a scratch native owner
when `FN_NATIVE_DEVELOPER_HOST` and `FN_NATIVE_TEST_ROOT` identify a frozen
image and its source snapshot.
