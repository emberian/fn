# Newsreaders

Any newsreader that can use TLS works with fn. tin, slrn and pan were tested
in September 2026. For reading in a browser instead, see
[the web reader](web.md). Words you may not know are in
[the short glossary](README.md#words-you-will-meet).

You need three things from the node's operator:

- the node's address and port;
- the node's certificate file, unless it uses a public one;
- your login and password (or an invitation code: see
  [accounts](operator.md#accounts-and-invitation-codes)).

Set your reader to use TLS (or STARTTLS), check the certificate, and log in.
The node refuses a login before the connection is encrypted.

## tin

tin 2.6 needs TLS from the very first byte. The node must have a TLS port.
The operator adds `tls_port` under `[listener]` in `fn.toml` and restarts.
For example (the node needs the group `control.cancel` for cancels to
work):

```toml
[listener]
host = "127.0.0.1"
port = 1119
tls_cert = "/srv/fn/tls/cert.pem"
tls_key = "/srv/fn/tls/key.pem"
tls_port = 1563

[auth]
required = true
protected_only = true
```

The node's log then shows `LISTENING-TLS 1563`.

On your side:

1. Use a tin built with `./configure --with-nntps=openssl`.
2. In `~/.tin/tinrc`, name the node's certificate:

   ```text
   tls_ca_cert_file=/home/reader/.fn/node-cert.pem
   ```

3. In `~/.newsauth` (mode 0600), put the server, password and login:

   ```text
   localhost PASSWORD guest
   ```

4. Start tin:

   ```sh
   NNTPSERVER=localhost tin -r -T -A -p 1563 -g localhost
   ```

If it goes wrong:

- The certificate must name the host tin dials. Do not use `-k`: it skips
  the check, and then the connection is not safe.
- tin refuses to post from a machine without a domain name
  (`Bad address in From: header`). Give it one: the build's `DOMAIN_NAME`,
  or `disable_sender=ON` in the site's `tin.defaults`.
- A cancel from tin (`D`, then `d`) withdraws your own post on a node set
  up with a `mission` (which serves `control.cancel`): readers then get
  `430 withdrawn`. tin may ask for a cancel secret: press Enter.

## Cancelling your own post

Use your reader's cancel command, logged in as yourself. The post
disappears on this node, and on peers that get the cancel. Another
login's cancel of your post is kept but does nothing. This was tested with tin and Thunderbird.
pan cancels only a post whose Sender line matches your pan profile.

## slrn and pan

- slrn 1.0.3 does not check the node's certificate at all. Use it only on
  a network you trust.
- pan 0.162 reads trusted certificates from `SSL_CERT_DIR`. Add the node's
  certificate to your system's store, or start pan with
  `SSL_CERT_DIR=/etc/ssl/certs`.

The engineers' notes on the web reader's saved posts are in
[the engineers' reference](client-internals.md#local-human-reader).
