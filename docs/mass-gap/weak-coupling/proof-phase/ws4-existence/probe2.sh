#!/bin/bash
# ws4: read-only check whether the replay clone has a full build cache (no build is started)
S=~/ym-replay/YM/submissions/openai-20261028/submission
ls -la $S/.lake/build/lib/lean/Solution.olean $S/.lake/build/lib/lean/Construction.olean 2>&1
find $S/.lake/build/lib/lean -name '*.olean' 2>/dev/null | wc -l
ls ~/.elan/toolchains 2>/dev/null
cat ~/ym-replay/stage1.log | head -20
ls ~/ym-replay/YM/docs
