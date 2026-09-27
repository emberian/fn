# The web reader

The web reader lets you read and post on an fn node from your browser. It
runs on your own computer and shows pages only to that computer. Words you
may not know are in [the short glossary](README.md#words-you-will-meet).

## Starting it

You need Python 3 (nothing else), the node's address, its certificate file
and your login. The web reader is not in the release: it is
`tools/fn_web.py` in fn's source, and it needs the files beside it in
`tools/`. On your own computer:

1. Get fn's source once, the node's certificate from its operator, and make
   two folders:

   ```sh
   git clone https://github.com/emberian/fn ~/fn
   mkdir -p ~/.fn ~/.fn-web
   cp cert.pem ~/.fn/news-cert.pem      # the file the operator gave you
   ```

2. Start the reader. `--node` is the node's name and its **plain** port
   (119, or the `--port` its operator chose): the reader switches to TLS
   itself (STARTTLS). The TLS-only port (563) does not work here:

   ```sh
   cd ~/fn
   python3 tools/fn_web.py --node news.example.org:119 --tls-cert ~/.fn/news-cert.pem \
     --user carol --outbox ~/.fn-web/outbox
   ```

3. Type your password when asked. (Or set `FN_CLIENT_PASSWORD`, or use
   `--credentials FILE` with a `user password` file only you can read.)

4. You will see:

   ```
   fn web client: carol at news.example.org:119 · TLSv1.3, certificate verified; open http://127.0.0.1:8919/
   ```

   Open that address in your browser.

If it does not start, the exit code says why: `1` the node refused the
login or the certificate did not match, `3` the node could not be reached,
`2` no password or a wrong option.

The password stays in the reader's memory. It is never written to a file,
page or log.

## Using it

- **Groups** (the home page) lists each group with how many articles you
  have not opened.
- **A group** shows its articles, newest window of 40 first, with replies
  indented under what they answer. A red dot marks articles you have not
  opened. "Older" and "Newer" move through the group.
- **An article** shows the text, who it claims to be from, and whether the
  node says it was signed. The From line is a claim, not a proof.
- **Reply** fills in the subject and the thread for you.
- **Conversation** shows a whole thread.
- **A withdrawn article** says so. It existed and may have been read;
  copies elsewhere are not erased.

Your read marks are kept on this computer only, in `~/.fn-web/`. The node
does not know what you have read.

## After you post

You will see one of three pages:

- **accepted** (green): the node saved it.
- **refused** (pink): the node did not save it, and shows why. "Edit as a new
  post" lets you fix it and try again.
- **uncertain** (yellow): the post may or may not have been saved. **Do not
  post it again as new.** Use "Re-send this same article to settle it". This
  is always safe: it never makes a second copy.

Refreshing a result page never posts again.

## Options

- `--outbox DIR` keeps your posts and drafts across restarts, so an
  uncertain post can still be settled later. The folder's parent must
  exist. It holds up to 128 records. When full, stop the reader and move old
  records out.
- `--port N`: the local port (default 8919).
- `--from 'Name <you@example.org>'`: your From line.
- `--keyring FILE`: authors' public keys you trust. Then each article is
  also checked here, not only by the node (see
  [checking a signature](agents.md#checking-a-signature-yourself)).
- `--marks FILE` moves the read marks. `--no-marks` keeps none.
- `--plain`: no encryption and no login, for a test node on your own
  machine only:

  ```sh
  python3 tools/fn_web.py --node 127.0.0.1:1119 --plain --port 8919
  ```

- One login per reader. To read as someone else, start another with
  `--user` and another `--port`.

`--node` with a host name works only if the node's certificate carries that
name.

## Safety

The reader answers only this computer (`127.0.0.1`). It refuses requests
from other websites, and every form carries a secret token. Anyone logged in
to this computer could use it, so do not run it on a shared machine.

Posts from the web reader are not signed. The node shows them as `absent`
(no signature).
