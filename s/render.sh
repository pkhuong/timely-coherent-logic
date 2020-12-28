#!/bin/sh

BASE=$(dirname "$(readlink -f "$0")")

OUT=${1:-"tcl.html"}

BRANCH_URL="https://github.com/pkhuong/timely-coherent-logic/tree/$(git rev-parse --abbrev-ref HEAD)"
REF=$(git rev-parse --short=16 HEAD)

echo "Rendering to $OUT"

git log empty..HEAD --reverse --color=always \
    --stat --full-index --compact-summary | \
    python3 "$BASE/render.py" | \
    pandoc -o "$OUT" -H "$BASE/modest.css" --toc \
           --from markdown+smart --to html5 --standalone \
           --metadata title="Timely Coherent Logic" \
           --metadata subtitle="$REF @ $BRANCH_URL" \
           --metadata "date=$(date)"
