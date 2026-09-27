#!/usr/bin/env python3
"""Drive stock slrn or pan against an fn node, inside the newsreader container.

    python3 drive.py slrn|pan --port P --user U --password-file F --group G
        [--second-group G2] --wire LOG --out DIR

Test tool (reader-clients-2 lane), run by tools/reader_clients_phase.py in
the container built from tools/reader_clients/Dockerfile (Debian slrn 1.0.3,
pan 0.162, Xvfb, xdotool, tmux).  The client connects to 127.0.0.1:P, the
phase's TLS relay, whose certificate the scratch CA issued; entry.sh has put
that CA into the container's system trust store.  pan verifies it (trust 0,
SSL_CERT_DIR=/etc/ssl/certs, pan/data/cert-store.cc); slrn 1.0.3 never
verifies a certificate (its OpenSSL path has no SSL_CTX_set_verify), which
is a client property this driver records, not something it can change.

Keystrokes only, as a user would type them: slrn in a tmux pane (the pane
text is the prompt oracle), pan under Xvfb through xdotool (the window
titles are the oracle).  Whether the node did the thing is read from the
relay's wire log, never from the client's screen: each action is bracketed
by a `--- action NAME` line appended to that log, and
v0_matrix.client_wire_outcomes reads the node's reply lines between them.
Prints one JSON object: per action what was typed, what was waited for and
whether it appeared.  Decides no verdict.
"""
import argparse
import json
import os
import re
import shlex
import subprocess
import sys
import time
from pathlib import Path

SUBJECT = "{} in the fn reader-clients matrix"
BODY = "a line from {} in the fn reader-clients matrix"


class Wire:
    """The relay's log: append action markers, wait for the node's replies."""

    def __init__(self, path):
        self.path = Path(path)

    def mark(self, name):
        with open(self.path, "a", encoding="utf-8") as out:
            out.write("%.3f 0 --- action %s\n" % (time.time(), name))
        return self.size()

    def size(self):
        return self.path.stat().st_size if self.path.exists() else 0

    def since(self, offset):
        with open(self.path, "rb") as log:
            log.seek(offset)
            return log.read().decode("utf-8", "replace")

    def wait(self, offset, pattern, timeout=60):
        deadline = time.monotonic() + timeout
        regex = re.compile(pattern, re.M)
        while time.monotonic() < deadline:
            match = regex.search(self.since(offset))
            if match:
                return match.group(0)
            time.sleep(0.3)
        return None

    def posted(self, offset, timeout=60):
        """The node's final line for the first POST after offset, or None."""
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            text = self.since(offset)
            match = re.search(r"^\S+ (\d+) C: POST$", text, re.M)
            if match:
                conn = match.group(1)
                replies = re.findall(r"^\S+ %s S: (.*)$" % conn, text[match.end():], re.M)
                if replies and not replies[0].startswith("340"):
                    return replies[0]
                if len(replies) > 1:
                    return replies[1]
            time.sleep(0.3)
        return None


def run(command, timeout=30):
    return subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          timeout=timeout, check=False).stdout.decode("utf-8", "replace")


# -- slrn --------------------------------------------------------------------

SHOTS = [0]


class Pane:
    def __init__(self, session, out):
        self.session, self.out = session, out

    def text(self):
        return run(["tmux", "capture-pane", "-p", "-t", self.session])

    def shot(self, name):
        SHOTS[0] += 1
        (self.out / "{:02d}-{}.txt".format(SHOTS[0], name)).write_text(self.text())

    def keys(self, *keys, literal=False):
        run(["tmux", "send-keys", "-t", self.session] + (["-l"] if literal else [])
            + list(keys))

    def wait(self, pattern, timeout=60):
        deadline, regex = time.monotonic() + timeout, re.compile(pattern, re.M)
        while time.monotonic() < deadline:
            match = regex.search(self.text())
            if match:
                return match.group(0)
            time.sleep(0.3)
        return None

    def answer(self, prompts, done, timeout=90):
        """Answer each prompt in `prompts` (regex -> keys) until `done()` holds."""
        deadline, seen = time.monotonic() + timeout, []
        while time.monotonic() < deadline:
            result = done()
            if result:
                return result, seen
            text = self.text().rstrip().splitlines()
            last = text[-1] if text else ""
            for pattern, keys in prompts:
                if re.search(pattern, last):
                    seen.append(last.strip())
                    if isinstance(keys, tuple):
                        self.keys(keys[0], literal=True)
                        self.keys("Enter")
                    else:
                        self.keys(keys)
                    time.sleep(1.0)
                    break
            else:
                time.sleep(0.3)
        return None, seen


def slrn(args, wire, out):
    home = out / "home"
    home.mkdir(parents=True, exist_ok=True)
    password = Path(args.password_file).read_text().strip()
    host = "snews://127.0.0.1"
    (home / ".slrnrc").write_text(
        'set username "{u}"\nset hostname "matrix.example.invalid"\n'
        'set realname "{u}"\nnnrpaccess "{h}" "{u}" "{p}"\n'
        'set force_authentication 1\nset read_active 1\n'
        'set editor_command "{home}/editor.sh \'%s\'"\n'
        'set cansecret_file "{home}/cansecret"\n'.format(
            u=args.user, h=host, p=password, home=home))
    (home / ".slrnrc").chmod(0o600)
    (home / "cansecret").write_text("a cancel-lock secret for the fn matrix\n")
    editor = home / "editor.sh"
    editor.write_text("#!/bin/sh\necho '{}' >> \"$1\"\n".format(BODY.format("slrn")))
    editor.chmod(0o755)
    groups = [g for g in (args.group, args.second_group) if g]
    (home / "newsrc").write_text("".join("{}:\n".format(g) for g in groups))
    # slrn's own NEWGROUPS stamp (group.c): a day before this run, so the
    # groups the phase created are new since it (RFC 3977 section 7.3).
    yesterday = time.gmtime(time.time() - 86400)
    (home / "newsrc.time").write_text(time.strftime("NEWGROUPS %y%m%d %H%M%S GMT\n", yesterday))
    base = "env HOME={} TERM=xterm slrn --nntp -h {} -p {} -k".format(
        shlex.quote(str(home)), host, args.port)
    result = {"client": run(["slrn", "--version"]).splitlines()[0], "actions": {}}
    acts = result["actions"]

    def session(name, command):
        run(["tmux", "kill-session", "-t", name])
        run(["tmux", "new-session", "-d", "-s", name, "-x", "132", "-y", "40",
             command + " 2>{}/{}.stderr; echo SLRN-EXITED $?; sleep 600".format(out, name)])
        return Pane(name, out)

    # 1. --create: slrn builds its newsrc from LIST (the first-run path).
    offset = wire.mark("create")
    pane = session("slrncreate", base + " --create -f {}/newsrc-create".format(home))
    reached = pane.wait(r"News Groups:|SLRN-EXITED|Failed to initialize", 60)
    pane.shot("create")
    acts["create"] = {"reached": reached, "completed": bool(reached and "News Groups" in reached),
                      "pane_tail": [l for l in pane.text().splitlines() if l.strip()][-6:]}
    run(["tmux", "kill-session", "-t", "slrncreate"])

    # 2. read: select the group, open the first unread article.
    offset = wire.mark("read")
    pane = session("slrn", base + " -f {}/newsrc".format(home))
    ready = pane.wait(r"News Groups:", 90)
    pane.shot("groups")
    act = {"groups_screen": bool(ready)}
    if ready:
        # Put the cursor on the group: slrn lists a group NEWGROUPS reports
        # as new ("N") first, so the first line is not always args.group.
        for _ in range(8):
            if re.search(r"^->\S*\s+\d+\s+{}\s*$".format(re.escape(args.group)),
                         pane.text(), re.M):
                break
            pane.keys("Down")
            time.sleep(0.5)
        act["cursor"] = [l for l in pane.text().splitlines() if l.startswith("->")][:1]
        pane.keys("Space")
        act["group"] = pane.wait(r"Group: {}".format(re.escape(args.group)), 60)
        pane.keys("Space")
        act["article"] = wire.wait(offset, r"C: (ARTICLE|BODY)[^\n]*\n[^\n]* S: \d{3}[^\n]*", 60)
        pane.shot("read")
    acts["read"] = act
    if not ready:
        return result

    # 3. reply: follow up to the article on screen.
    offset = wire.mark("reply")
    pane.keys("f")
    # A follow-up to a cross-post asks where it goes: this group (all
    # groups draws slrn's netiquette refusal without Followup-To).
    final, seen = pane.answer([(r"followup\?", "y"), (r"Post the message\?", "y"),
                               (r"^Crosspost using:", "t"),
                               (r"[Cc]ontinue\?", "y")],
                              lambda: wire.posted(offset, timeout=0.1), 90)
    pane.shot("reply")
    acts["reply"] = {"prompts": seen, "node": final}

    # 4. Xref: back in the group list, is the cross-post still unread in G2?
    wire.mark("xref")
    pane.keys("q")
    pane.wait(r"News Groups:", 30)
    time.sleep(1)
    pane.shot("xref")
    screen = pane.text()
    unread = None
    if args.second_group:
        match = re.search(r"^\S*\s+(\d+)\s+{}\s*$".format(re.escape(args.second_group)),
                          screen, re.M)
        unread = int(match.group(1)) if match else 0
    acts["xref"] = {"second_group": args.second_group, "unread_in_second_group": unread,
                    "listed_lines": [l.strip() for l in screen.splitlines()
                                     if re.search(r"^\S*\s+\d+\s+\S", l)]}

    # 5. post a new article to the group under the cursor.
    offset = wire.mark("post")
    pane.keys("p")
    final, seen = pane.answer([(r"want to post\?", "y"), (r"^Newsgroup", "Enter"),
                               (r"^Subject:", (SUBJECT.format("slrn"),)),
                               (r"Post the message\?", "y")],
                              lambda: wire.posted(offset, timeout=0.1), 90)
    pane.shot("post")
    acts["post"] = {"prompts": seen, "node": final}

    # 6. cancel that article: refresh, enter the group, go to the last
    # article (the newest, ours), open it, ESC C-c.
    offset = wire.mark("cancel")
    pane.keys("G")
    pane.wait(r"News Groups:", 30)
    time.sleep(1)
    pane.keys("Space")
    act = {"group": pane.wait(r"Group: {}".format(re.escape(args.group)), 60)}
    pane.keys("Escape", ">")
    time.sleep(1)
    pane.keys("Space")
    act["opened"] = wire.wait(offset, r"S: Subject: {}".format(re.escape(SUBJECT.format("slrn"))),
                              30)
    pane.shot("cancel-open")
    if act["opened"]:
        pane.keys("Escape", "C-c")
        final, seen = pane.answer([(r"cancel this article\?", "y")],
                                  lambda: wire.posted(offset, timeout=0.1), 60)
        act.update(prompts=seen, node=final)
    pane.shot("cancel")
    acts["cancel"] = act
    wire.mark("quit")
    pane.keys("q")
    pane.answer([(r"quit\?", "y")], lambda: pane.wait("SLRN-EXITED", 0.1), 20)
    run(["tmux", "kill-session", "-t", "slrn"])
    return result


# -- pan ---------------------------------------------------------------------

class X:
    def __init__(self, out):
        self.out, self.shots = out, 0
        self.env = dict(os.environ, DISPLAY=":99")

    def do(self, *words):
        return subprocess.run(["xdotool"] + list(words), env=self.env, stdout=subprocess.PIPE,
                              stderr=subprocess.DEVNULL, timeout=30,
                              check=False).stdout.decode()

    def windows(self):
        """(id, name, width, height) of every visible window."""
        out = []
        for wid in self.do("search", "--onlyvisible", "--name", "").split():
            name = self.do("getwindowname", wid).strip()
            geometry = re.search(r"Geometry: (\d+)x(\d+)", self.do("getwindowgeometry", wid))
            if geometry:
                out.append((wid, name, int(geometry.group(1)), int(geometry.group(2))))
        return out

    def find(self, pattern, timeout=30, largest=True):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            hits = [w for w in self.windows() if re.search(pattern, w[1]) and w[2] > 100]
            if hits:
                hits.sort(key=lambda w: w[2] * w[3], reverse=largest)
                return hits[0]
            time.sleep(0.5)
        return None

    def dialogs(self, *keep):
        """Every other visible window: pan's transient dialogs, whose title is
        empty or their parent's, so they are told apart by id, not name."""
        keep = {w[0] for w in keep if w}
        return [w for w in self.windows() if w[2] > 100 and w[3] > 50 and w[0] not in keep
                and w[2] * w[3] < 1280 * 1024]

    def gone(self, pattern, timeout=30):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if not [w for w in self.windows() if re.search(pattern, w[1]) and w[2] > 300]:
                return True
            time.sleep(0.5)
        return False

    def keys(self, wid, *keys):
        self.do("windowfocus", "--sync", wid)
        for key in keys:
            self.do("key", "--clearmodifiers", key)
            time.sleep(0.8)

    def type(self, wid, text):
        self.do("windowfocus", "--sync", wid)
        self.do("type", "--delay", "15", text)

    def shot(self, name, wid="-root"):
        self.shots += 1
        path = self.out / "{:02d}-{}.png".format(self.shots, name)
        source = "-root" if wid == "-root" else "-id " + shlex.quote(wid)
        subprocess.run("xwd {} -silent | xwdtopnm 2>/dev/null | pnmtopng > {}".format(
            source, shlex.quote(str(path))), shell=True, env=self.env, timeout=30, check=False)
        return path.name

    def send(self, post, wire, offset, main, timeout=60):
        """Ctrl+Return in a compose window, then each dialog pan raises is
        photographed (its own window: without a window manager the root
        capture shows it black) and recorded; none is answered blindly."""
        self.keys(post[0], "ctrl+Return")
        deadline, dialogs = time.monotonic() + timeout, []
        while time.monotonic() < deadline:
            final = wire.posted(offset, timeout=1)
            if final:
                return final, dialogs
            for dialog in self.dialogs(main, post):
                if dialog[0] not in [d["id"] for d in dialogs]:
                    time.sleep(1.5)
                    dialogs.append({"id": dialog[0], "title": dialog[1],
                                    "shot": self.shot("dialog", dialog[0])})
        return None, dialogs


PAN_KEYS = {"group": ("read-next-unread-group", "g"), "next": ("read-next-article", "n"),
            "followup": ("followup-to", "f"), "post": ("post", "p"),
            "headers": ("get-new-headers-in-selected-groups", "a"),
            "cancel": ("cancel-article", "k")}


def key(name):
    return "ctrl+alt+" + PAN_KEYS[name][1]


def pan(args, wire, out):
    home = out / "home"
    home.mkdir(parents=True, exist_ok=True)
    password = Path(args.password_file).read_text().strip()
    address = "{}@matrix.example.invalid".format(args.user)
    (home / "servers.xml").write_text(
        '<?xml version="1.0" encoding="utf-8" ?>\n<server-properties>\n'
        '  <server id="1">\n    <host>127.0.0.1</host>\n    <port>{}</port>\n'
        '    <username>{}</username>\n    <password>{}</password>\n'
        '    <expire-articles-n-days-old>31</expire-articles-n-days-old>\n'
        '    <connection-limit>2</connection-limit>\n    <newsrc>newsrc-1</newsrc>\n'
        '    <rank>1</rank>\n    <use-ssl>1</use-ssl>\n    <trust>0</trust>\n'
        '    <compression-type>0</compression-type>\n    <cert></cert>\n'
        '  </server>\n</server-properties>\n'.format(args.port, args.user, password))
    (home / "servers.xml").chmod(0o600)
    (home / "preferences.xml").write_text(
        "<?xml version=\"1.0\" encoding=\"utf-8\" ?>\n<preferences>\n"
        "  <flag name='use-password-storage' value='false'/>\n"
        "  <flag name='spellcheck-enabled' value='false'/>\n"
        "  <flag name='get-new-headers-on-startup' value='true'/>\n</preferences>\n")
    (home / "posting.xml").write_text(
        '<?xml version="1.0" encoding="utf-8" ?>\n<posting>\n  <profiles>\n'
        '    <profile name="friend">\n      <username>{}</username>\n'
        '      <address>{}</address>\n      <server>1</server>\n    </profile>\n'
        '  </profiles>\n</posting>\n'.format(args.user, address))
    # Only the one group: selecting a group whose headers pan never fetched
    # opens its "get headers" dialog, which is not what this row measures.
    (home / "newsrc-1").write_text("{}: \n".format(args.group))
    # Accelerators with a modifier, the way a user edits accels.txt: pan's
    # own single-letter ones (G, n, f, p, A) are typed into the group tree's
    # type-ahead search when that pane has focus, and Cancel Article has no
    # accelerator at all (pan/gui/actions.cc); menus do not draw without a
    # window manager.  Same actions, other keys.
    (home / "accels.txt").write_text("".join(
        '(gtk_accel_path "<Actions>/Actions/{}" "<Primary><Alt>{}")\n'.format(action, key)
        for action, key in PAN_KEYS.values()))
    env = "env DISPLAY=:99 HOME={h} PAN_HOME={h} SSL_CERT_DIR=/etc/ssl/certs".format(
        h=shlex.quote(str(home)))
    run(["tmux", "kill-server"])
    run(["tmux", "new-session", "-d", "-s", "xvfb",
         "Xvfb :99 -screen 0 1280x1024x24 -nolisten tcp"])
    time.sleep(2)
    x = X(out)
    result = {"client": run(["sh", "-c", "dpkg-query -W -f '${Package} ${Version}' pan"]),
              "actions": {}}
    acts = result["actions"]

    def start():
        run(["tmux", "kill-session", "-t", "pan"])
        run(["tmux", "new-session", "-d", "-s", "pan",
             "{} pan >>{}/pan.stderr 2>&1; echo PAN-EXITED; sleep 600".format(env, out)])
        return x.find(r"^Pan", 60)

    # 1. read: pan fetches headers for its subscribed group at startup; then
    # Next Unread Group, and Next Article until the pan seed is on screen.
    offset = wire.mark("read")
    main = start()
    act = {"window": bool(main),
           "headers": wire.wait(offset, r"C: X?OVER[^\n]*\n[^\n]* S: \d{3}[^\n]*", 60)}
    if main:
        # A key pressed while pan is still starting is dropped: try again.
        for _ in range(3):
            x.keys(main[0], key("group"))
            act["group"] = bool(x.find(r"^Pan: {}$".format(re.escape(args.group)), 10))
            if act["group"]:
                break
        # n until the article on screen is the phase's pan seed (the group
        # also holds the other clients' seeds).
        for _ in range(5):
            mark = wire.size()
            x.keys(main[0], key("next"))
            act["article"] = wire.wait(
                offset, r"C: (ARTICLE|BODY)[^\n]*\n[^\n]* S: \d{3}[^\n]*", 30)
            act["seed_on_screen"] = bool(wire.wait(mark, r"S: Subject: seed for pan$", 10))
            if act["seed_on_screen"]:
                break
        x.shot("read")
    acts["read"] = act
    if not main:
        return result

    # 2. cancel the article on screen (the phase's seed, which carries a
    # Sender header: pan 0.162 matches the Sender, not From, against its
    # profiles, pan/gui/gui.cc do_cancel_article).
    offset = wire.mark("cancel")
    x.keys(main[0], key("cancel"))
    act = {}
    post = x.find(r"^Post Article", 15)
    time.sleep(2)
    x.shot("cancel-compose")
    # pan puts a modal "Send this article to ask your server to cancel"
    # note over the compose window; it has to go first (it is photographed,
    # then dismissed with its one button).
    act["notes"] = []
    for _ in range(3):
        notes = x.dialogs(main, post)
        if not notes:
            break
        for dialog in notes:
            act["notes"].append(x.shot("cancel-note", dialog[0]))
            x.keys(dialog[0], "Return")
        time.sleep(1)
    act["window"] = bool(post)
    if post:
        # pan builds the cancel with the body "Ignore / Article canceled by
        # author", but its compose view shows the body empty and its own
        # check refuses to send ("Error: Message is empty.",
        # usenet-utils/message-check.cc check_empty); a user types a line.
        x.type(post[0], "Ignore")
        act["node"], act["dialogs"] = x.send(post, wire, offset, main)
        act["closed"] = x.gone(r"^Post Article")
    else:
        act["refused_by_client"] = [w[1] for w in x.windows()]
        for dialog in x.dialogs(main):
            x.keys(dialog[0], "Return")
    x.shot("cancel")
    acts["cancel"] = act

    # 3. reply to the same article.
    offset = wire.mark("reply")
    for _ in range(3):
        x.keys(main[0], key("followup"))
        post = x.find(r"^Post Article", 10)
        if post:
            break
    act = {"window": bool(post)}
    if post:
        x.type(post[0], "\n" + BODY.format("pan"))
        x.shot("reply-compose")
        act["node"], act["dialogs"] = x.send(post, wire, offset, main)
        act["closed"] = x.gone(r"^Post Article")
    acts["reply"] = act

    # 4. post a new article.
    offset = wire.mark("post")
    time.sleep(2)
    for _ in range(3):
        x.keys(main[0], key("post"))
        post = x.find(r"^Post Article", 10)
        if post:
            break
    act = {"window": bool(post)}
    if post:
        x.type(post[0], SUBJECT.format("pan"))
        x.keys(post[0], "Tab", "Tab", "Tab")
        x.type(post[0], BODY.format("pan"))
        x.shot("post-compose")
        act["node"], act["dialogs"] = x.send(post, wire, offset, main)
        act["closed"] = x.gone(r"^Post Article")
    acts["post"] = act

    # 5. refresh: pan's "get new headers" on its open connections.  What the
    # node says to GROUP here is the R1 measurement (PKT-571): a connection
    # opened before the post keeps the view it pinned.
    offset = wire.mark("refresh")
    time.sleep(2)
    x.keys(main[0], key("headers"))
    time.sleep(8)
    text = wire.since(offset)
    acts["refresh"] = {"group_replies": re.findall(
        r"^\S+ (\d+) S: (211 [^\n]*)$", text, re.M),
        "over": re.findall(r"^\S+ (\d+) C: (X?OVER [^\n]*)$", text, re.M)}
    x.shot("refresh")
    wire.mark("quit")
    x.keys(main[0], "ctrl+q")
    time.sleep(3)
    run(["tmux", "kill-server"])
    return result


# -- tin ---------------------------------------------------------------------

def tin(args, wire, out):
    """Debian tin (NNTPS-able) in a tmux pane: read, follow up, post, cancel.

    tin 2.6 talks TLS from the first byte (-T) to the relay, logs in with
    AUTHINFO when asked (-A, ~/.newsauth: `server password user`), and
    reads its newsrc from ~/.newsrc.  The editor appends one body line; the
    post prompt is answered `p`."""
    home = out / "tinhome"
    home.mkdir(parents=True, exist_ok=True)
    password = Path(args.password_file).read_text().strip()
    (home / ".newsauth").write_text("127.0.0.1 {} {}\n".format(password, args.user))
    (home / ".newsauth").chmod(0o600)
    groups = [g for g in (args.group, args.second_group) if g]
    (home / ".newsrc").write_text("".join("{}:\n".format(g) for g in groups))
    tindir = home / ".tin"
    tindir.mkdir(exist_ok=True)
    # No first-run questions, no confirmation of quitting, the editor ours.
    (tindir / "tinrc").write_text(
        "confirm_choice=0\nauto_reconnect=ON\nshow_description=OFF\n"
        "use_mouse=OFF\nbeginner_level=OFF\nshow_only_unread_arts=OFF\n"
        "default_editor_format=%E %F\nshow_signatures=OFF\n")
    editor = home / "editor.sh"
    editor.write_text("#!/bin/sh\necho '{}' >> \"$1\"\n".format(BODY.format("tin")))
    editor.chmod(0o755)
    base = ("env HOME={h} TERM=xterm EDITOR={e} VISUAL={e} NNTPSERVER=127.0.0.1 "
            "tin -r -T -A -p {p} -q -d".format(h=shlex.quote(str(home)),
                                                 e=shlex.quote(str(editor)), p=args.port))
    version = run(["tin", "-V"]).splitlines()
    result = {"client": version[0] if version else "tin", "features":
              [l.strip() for l in version if "NNTP" in l][:1], "actions": {}}
    acts = result["actions"]
    run(["tmux", "kill-session", "-t", "tin"])
    run(["tmux", "new-session", "-d", "-s", "tin", "-x", "132", "-y", "40",
         base + " 2>{}/tin.stderr; echo TIN-EXITED $?; sleep 600".format(out)])
    pane = Pane("tin", out)
    offset = wire.mark("read")
    ready = pane.wait(r"Group Selection|TIN-EXITED", 90)
    pane.shot("groups")
    act = {"groups_screen": bool(ready and "Group Selection" in ready)}
    acts["read"] = act
    if not act["groups_screen"]:
        act["pane_tail"] = [l for l in pane.text().splitlines() if l.strip()][-8:]
        return result
    # The cursor to args.group, then into it and open the first thread.
    pane.keys("g")
    pane.answer([(r"[Gg]roup", (args.group,))], lambda: pane.wait(
        r"{}".format(re.escape(args.group)), 0.1), 10)
    time.sleep(1)
    pane.keys("Enter")
    act["group"] = pane.wait(r"{}".format(re.escape(args.group)), 30)
    time.sleep(1)
    pane.keys("Enter")
    act["article"] = wire.wait(offset, r"C: (ARTICLE|BODY|HEAD)[^\n]*\n[^\n]* S: \d{3}[^\n]*", 60)
    pane.shot("read")

    # follow up to the article on screen
    offset = wire.mark("reply")
    pane.keys("f")
    final, seen = pane.answer([(r"[Pp]ost.*followup.*\?|[Qq]uote", "y"),
                               (r"q\)uit, e\)dit.*p\)ost|p\)ost.*:", "p"),
                               (r"[Cc]ontinue\?|[Aa]re you sure", "y")],
                              lambda: wire.posted(offset, timeout=0.1), 90)
    pane.shot("reply")
    acts["reply"] = {"prompts": seen, "node": final}

    # post a new article to the group
    offset = wire.mark("post")
    pane.keys("q")
    time.sleep(1)
    pane.keys("w")
    final, seen = pane.answer([(r"[Ss]ubject", (SUBJECT.format("tin"),)),
                               (r"q\)uit, e\)dit.*p\)ost|p\)ost.*:", "p"),
                               (r"[Cc]ontinue\?|[Aa]re you sure", "y")],
                              lambda: wire.posted(offset, timeout=0.1), 90)
    pane.shot("post")
    acts["post"] = {"prompts": seen, "node": final}

    # cancel it: rescan, last article, D (delete/cancel), confirm.
    offset = wire.mark("cancel")
    time.sleep(2)
    pane.keys("C-r")                                   # reread the group
    time.sleep(3)
    pane.keys("End")
    time.sleep(1)
    pane.keys("Enter")
    act = {"opened": wire.wait(offset, r"S: Subject: {}".format(
        re.escape(SUBJECT.format("tin"))), 30)}
    pane.shot("cancel-open")
    if act["opened"]:
        pane.keys("D")
        final, seen = pane.answer([(r"[Cc]ancel.*\?|[Dd]elete", "d"),
                                   (r"q\)uit, e\)dit.*p\)ost|p\)ost.*:|[Cc]ancel.*\[", "p"),
                                   (r"[Aa]re you sure|[Cc]ontinue\?", "y")],
                                  lambda: wire.posted(offset, timeout=0.1), 60)
        act.update(prompts=seen, node=final)
    pane.shot("cancel")
    acts["cancel"] = act
    wire.mark("quit")
    pane.keys("Q")
    pane.answer([(r"[Qq]uit.*\?|[Ee]xit.*\?", "y")], lambda: pane.wait("TIN-EXITED", 0.1), 20)
    run(["tmux", "kill-session", "-t", "tin"])
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("client", choices=("slrn", "pan", "tin"))
    parser.add_argument("--port", type=int, required=True)
    parser.add_argument("--user", required=True)
    parser.add_argument("--password-file", required=True)
    parser.add_argument("--group", required=True)
    parser.add_argument("--second-group", default="")
    parser.add_argument("--wire", required=True)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    wire = Wire(args.wire)
    try:
        result = {"slrn": slrn, "pan": pan, "tin": tin}[args.client](args, wire, out)
    except Exception as error:                          # noqa: BLE001
        result = {"error": "{}: {}".format(type(error).__name__, error)}
    print(json.dumps(result, default=str))
    return 0


if __name__ == "__main__":
    sys.exit(main())
