# The newsreader container for tools/reader_clients_phase.py: stock Debian
# slrn, pan and tin (NNTPS-able: hbox's own tin 2.6.2 is not), Xvfb and xdotool to type at pan, tmux to type at slrn,
# x11-apps and netpbm for screenshots.  The scratch CA is added to the
# system trust store at run time (entry.sh), never baked in.
FROM debian:trixie-slim
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
      slrn pan tin xvfb xauth xdotool x11-utils x11-apps netpbm tmux ca-certificates openssl \
      python3 dbus-x11 procps && rm -rf /var/lib/apt/lists/*
COPY entry.sh /usr/local/bin/fn-reader-entry
RUN chmod 755 /usr/local/bin/fn-reader-entry
ENTRYPOINT ["/usr/local/bin/fn-reader-entry"]
