#!/usr/bin/env python3
from collections import namedtuple
import fileinput
import re


URL_BASE = "https://github.com/pkhuong/timely-coherent-logic/commit/"

URL_SUFFIX = "?diff=unified#toc"


DEFAULT_SECTION_HEADER = "#### "


def segment_log(lines):
    """Breaks up commits from `git log --stat --full-index --compact-summary --color=aways`"""
    acc = []
    for line in lines:
        line = line[:-1]  # drop trailing \n
        if re.match(r"^(\x1b.*)?commit [a-f0-9]+(\x1b.*)?( [(].*[)])?$", line):
            if acc:
                yield acc
            acc = []
        acc.append(line)
    if acc:
        yield acc


Commit = namedtuple("Commit", ["sha", "props", "title", "body", "summary"])


def parse_all_segments(segments):
    return map(parse_segment, segments)


def parse_segment(lines):
    """
    Input looks like

    ESC[33mcommit a33d31f8a53788b4df2e1c4acdedb6f27f1b179bESC[m
    Author: Paul Khuong <pvk@pvk.ca>
    Date:   Mon Jan 18 14:42:46 2021 -0500

        foo

     README.md | 2 ESC[32m+ESC[mESC[31m-ESC[m
     1 file changed, 1 insertion(+), 1 deletion(-)
    """
    lines = list(reversed(lines))
    sha = re.match(r"^(\x1b.*)?commit ([a-f0-9]+)(\x1b.*)?$", lines[-1]).group(2)
    lines.pop()
    props = dict()
    while lines:
        prop_match = re.match("^(.+):\s+(.+)$", lines[-1])
        if not prop_match:
            break
        props[prop_match.group(1)] = prop_match.group(2)
        lines.pop()
    if not lines:
        return Commit(sha, props, "", "")
    # Should be one empty line before the commit message.
    assert lines[-1] == ""
    lines.pop()
    body = []
    while lines:
        line = lines[-1]
        if line == "":
            body.append(line)
            lines.pop()
            continue
        body_match = re.match("^\s{4}(.*)$", line)
        if not body_match:
            break
        body.append(body_match.group(1))
        lines.pop()
    summary = list(reversed(lines))
    if body:
        title = body[0]
        body = body[1:]
    else:
        title = ""
    return Commit(sha, props, title, "\n".join(body), "\n".join(summary))


def ansi2html(text):
    """We only have to convert +/- stats lines.  These look like

    \x1b[32m+++++\x1b[m\x1b[31m-----\x1b[m"""
    text = re.sub(r"\x1b\[32m", "<span style='color: green'>", text)
    text = re.sub(r"\x1b\[31m", "<span style='color: red'>", text)
    text = re.sub(r"\x1b\[m", "</span>", text)
    return text


def htmlify_stats(commits):
    for commit in commits:
        yield commit._replace(summary=ansi2html(commit.summary))


def commit_to_markdown(commit):
    url = URL_BASE + commit.sha + URL_SUFFIX
    section_header = DEFAULT_SECTION_HEADER
    title = commit.title
    # We want commit titles like `# Foo` for markdown headers, but
    # that clashes with git's comment syntax.  Hack around that by
    # treating `.#...` like `#...`, but only in the title line.
    if re.match("^\.#", title):
        title = title[1:]
    # Override the section header prefix if there is one.
    match = re.match("^(#+)(.*)$", title)
    if match:
        section_header = match.group(1)
        title = match.group(2)
    # If there's a summary, it's a non-empty diff, and not just a
    # commit message.
    if commit.summary:
        title = "%s %s <a href='%s'>(diff)</a>" % (section_header, title, url)
        summary = (
            "\n\n<details><summary>Commit summary <a href='%s'>(GH)</a></summary><pre>%s</pre></details>"
            % (url, commit.summary)
        )
    else:
        title = "%s %s" % (section_header, title)
        summary = ""
    return title + "\n\n" + commit.body + summary


def markdownify_commits(commits):
    return map(commit_to_markdown, commits)


if __name__ == "__main__":
    for md in markdownify_commits(
        htmlify_stats(parse_all_segments(segment_log(fileinput.input())))
    ):
        print("%s" % md)
