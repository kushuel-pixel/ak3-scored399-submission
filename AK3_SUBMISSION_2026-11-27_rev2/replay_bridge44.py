#!/usr/bin/env python3
"""Replay the ordered fixed ac-00399 witness using the 14 ac-r2-v1 moves."""
START = ("YXYxyx", "YYYYxxx")
A = ("xyxYXY", "xxxYYYY")
S = ("XyyyxYYYY", "xxYYYYYXyyyyy")
NORMALIZE = (6,8,6,10,10,10)
MOVES = (7,10,5,6,5,6,8,12,0,2,6,1,4,1,9,7,5,12,12,11,5,12,4,10,12,11,5,12,11,5,12,4,10,12,12,12,6,4,13,13,8,8,8,7)
INVERSE = (0,1,3,2,5,4,7,6,9,8,11,10,13,12)
def inv(w):
    return w[::-1].swapcase()
def reduce_word(w):
    stack = []
    for c in w:
        if stack and stack[-1] == c.swapcase():
            stack.pop()
        else:
            stack.append(c)
    return "".join(stack)
def step(state, i):
    r,s = state
    if not 0 <= i < 14:
        raise ValueError(i)
    if i == 0: r = inv(r)
    elif i == 1: s = inv(s)
    elif i == 2: r += s
    elif i == 3: r += inv(s)
    elif i == 4: s += r
    elif i == 5: s += inv(r)
    else:
        c = "xXyY"[(i-6)%4]
        if i < 10: r = c + r + inv(c)
        else: s = c + s + inv(c)
    return reduce_word(r), reduce_word(s)
def trace(start, ids):
    out = [start]
    for i in ids:
        out.append(step(out[-1], i))
    return out
def check():
    walk = trace(START, MOVES)
    peak = max(len(r)+len(s) for r,s in walk)
    if not (len(MOVES)==44 and len(walk)==45 and walk[-1]==S and
            peak==sum(map(len,S))==22 and trace(START,NORMALIZE)[-1]==A and
            trace(S,[INVERSE[i] for i in reversed(MOVES)])==walk[::-1]):
        raise SystemExit("FAIL: witness, peak, or reverse replay")
    return walk
if __name__ == "__main__":
    import sys
    rows = check()
    if "--tsv" in sys.argv[1:]:
        print("step\tmove_id\tfirst\tsecond\ttotal_length")
        for j,(r,s) in enumerate(rows):
            print(j,MOVES[j-1] if j else "",r,s,len(r)+len(s),sep="\t")
    else:
        print("PASS: 44 moves; 45 states; endpoint S; peak 22; normalization and reverse replay match.")
