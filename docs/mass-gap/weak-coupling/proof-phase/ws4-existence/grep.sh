#!/bin/bash
# ws4: read-only grep in the OpenAI submission source. Usage: grep.sh <pattern> [subdir] [maxlines]
S=~/ym-replay/YM/submissions/openai-20261028/submission
cd $S
grep -rnE --include='*.lean' "$1" ${2:-.} --exclude-dir=.lake | head -${3:-40}
