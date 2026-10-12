"""Git subprocesses for scratch repositories, independent of user signing config."""
from __future__ import annotations

import os
from pathlib import Path
import subprocess


def run(command, **kwargs):
    """Run Git with isolated config; persist unsigned commits/tags on init/clone.

    Keep the caller's environment (identities, merge drivers and test stubs),
    removing inherited command-scope overrides and global/system config sources.
    Local settings also cover tools under test that invoke Git themselves
    in the resulting repository.
    """
    env = dict(os.environ if kwargs.get("env") is None else kwargs["env"])
    for name in list(env):
        if (name in ("GIT_CONFIG_COUNT", "GIT_CONFIG_PARAMETERS")
                or name.startswith(("GIT_CONFIG_KEY_", "GIT_CONFIG_VALUE_"))):
            del env[name]
    env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_SYSTEM=os.devnull,
               GIT_CONFIG_NOSYSTEM="1")
    kwargs["env"] = env
    kwargs.setdefault("timeout", 60)
    answer = subprocess.run(command, **kwargs)
    words = list(command)
    index = 1
    root = Path(kwargs.get("cwd") or Path.cwd())
    while index < len(words) and words[index].startswith("-"):
        option = words[index]
        if option in ("-C", "-c", "--git-dir", "--work-tree"):
            value = words[index + 1]
            if option == "-C":
                root = root / value
            index += 2
        else:
            index += 1
    if answer.returncode == 0 and index < len(words) and words[index] in ("init", "clone"):
        # These fixtures use an optional init destination or an explicit clone
        # destination. Skip the options that take a following argument.
        args = iter(words[index + 1:])
        destinations = []
        for arg in args:
            if arg in ("-b", "--initial-branch", "--template", "--object-format", "-o", "--origin"):
                next(args)
            elif not arg.startswith("-"):
                destinations.append(arg)
        if destinations:
            root = root / destinations[-1]
        for setting in ("commit.gpgsign", "tag.gpgsign"):
            subprocess.run(["git", "-C", str(root), "config", "--local", setting, "false"],
                           env=env, check=True, capture_output=True, timeout=10)
    return answer
