#!/usr/bin/python3

import sys as sys

# is the extract field present ?
extr=1

for l in sys.stdin:
    ts = [int(i) for i in l.strip().split()]
    n     = ts[0]
    begt  = ts[1]
    # ts[8+extr] is total time
    steps = ts[2:8+extr] + [ts[9+extr]]
    endt  = ts[10+extr]
    print(n, end=" ")
    tsum = 0
    for i in steps:
        tsum += i
        print(tsum, end=" ")
    print(endt - begt)
