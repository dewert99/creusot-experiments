#!/bin/bash
#sed -i 's/  use seq.Seq/  use seq.Seq\n  use seq.FreeMonoid/g' $1
wsl bash -lic "why3 prove $1 --debug=ignore_unused_vars -L ../creusot/prelude/ -P z3_no_mbqi -a split_vc -a eliminate_algebraic_if_poly -t 5 --color " #| grep -B 3 "Timeout\|Invalid\|Unknown" | sed 's/\n/\r\n/'
#ARG="$1"
#shift
#rm //wsl.localhost/Ubuntu-22.04/tmp/pass-why3-temp.mlcfg
#cp $ARG //wsl.localhost/Ubuntu-22.04/tmp/pass-why3-temp.mlcfg
#wsl bash why3.sh $@