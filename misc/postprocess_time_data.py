#!/usr/bin/python3

import sys as sys

# is the extract field present ?
extr=1

for l in sys.stdin:
    ts = [int(i) for i in l.strip().split()]
    n     = ts[0]
    begt  = ts[1]
    # we swap M and lin_cond ts[9+extr] is total time
    steps = [ts[2], ts[4], ts[3]] + ts[5:9+extr] + [ts[10+extr]]
    endt  = ts[11+extr]
    print(n, end=" ")
    tsum = 0
    for i in steps:
        tsum += i
        print(tsum/1e3, end=" ")
    print((endt - begt)/1e3)
