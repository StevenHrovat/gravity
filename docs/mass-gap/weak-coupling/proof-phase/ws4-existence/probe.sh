#!/bin/bash
# ws4: read-only probe of the local ym-replay clone
R=~/ym-replay/YM
cd $R && git log -1 --format='%H %ci %s' 2>&1
ls $R; echo ---
S=$R/submissions/openai-20261028/submission
ls $S; echo ---
cat $S/lean-toolchain
find $S -maxdepth 1 -name '*.lean' | head
ls $S/YangMills 2>/dev/null | head -80
echo --- count
find $S -name '*.lean' -not -path '*/.lake/*' | wc -l
ls $S/.lake/build/lib/lean 2>/dev/null | head
tail -5 ~/ym-replay/stage1.log
