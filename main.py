import itertools
import random
import re
import string
from collections import defaultdict, Counter
from functools import reduce
from operator import eq, neg

from sortedcontainers import SortedSet

import search
from utils import argmin_random_tie, count, first, extend
import findPairs
import time



measurements = {}

firstResultOK, secondResultOK, thirdResultOK, measure = findPairs.runFiles("rlfap/var11.txt", "rlfap/dom11.txt", "rlfap/ctr11.txt")

if firstResultOK and secondResultOK and thirdResultOK:
    measurements['files11 SAT'] = []
    for x, y in measure.items():
        measurements['files11 SAT'].append((x, round(y, 3)))
else:
    measurements['files11 UNSAT'] = []
    for x, y in measure.items():
        measurements['files11 UNSAT'].append((x, round(y, 3)))


firstResultOK, secondResultOK, thirdResultOK, measure = findPairs.runFiles("rlfap/var2-f24.txt", "rlfap/dom2-f24.txt", "rlfap/ctr2-f24.txt")

if firstResultOK and secondResultOK and thirdResultOK:
    measurements['files2-f24 SAT'] = []
    for x, y in measure.items():
        measurements['files2-f24 SAT'].append((x, round(y, 3)))
else:
    measurements['files2-f24 UNSAT'] = []
    for x, y in measure.items():
        measurements['files2-f24 UNSAT'].append((x, round(y, 3)))


firstResultOK, secondResultOK, thirdResultOK, measure = findPairs.runFiles("rlfap/var3-f10.txt", "rlfap/dom3-f10.txt", "rlfap/ctr3-f10.txt")

if firstResultOK and secondResultOK and thirdResultOK:
    measurements['files3-f10 SAT'] = []
    for x, y in measure.items():
        measurements['files3-f10 SAT'].append((x, round(y, 3)))
else:
    measurements['files3-f10 UNSAT'] = []
    for x, y in measure.items():
        measurements['files3-f10 UNSAT'].append((x, round(y, 3)))


firstResultOK, secondResultOK, thirdResultOK, measure = findPairs.runFiles("rlfap/var7-w1-f4.txt", "rlfap/dom7-w1-f4.txt", "rlfap/ctr7-w1-f4.txt")

if firstResultOK and secondResultOK and thirdResultOK:
    measurements['files7-w1-f4 SAT'] = []
    for x, y in measure.items():
        measurements['files7-w1-f4 SAT'].append((x, round(y, 3)))
else:
    measurements['files7-w1-f4 UNSAT'] = []
    for x, y in measure.items():
        measurements['files7-w1-f4 UNSAT'].append((x, round(y, 3)))


# secondResultOK, thirdResultOK, measure = findPairs.runFiles("rlfap/var8-f10.txt", "rlfap/dom8-f10.txt", "rlfap/ctr8-f10.txt")

# if secondResultOK and thirdResultOK:
#     measurements['files8-f10 SAT'] = []
#     for x, y in measure.items():
#         measurements['files8-f10 SAT'].append((x, round(y, 3)))
# else:
#     measurements['files8-f10 UNSAT'] = []
#     for x, y in measure.items():
#         measurements['files8-f10 UNSAT'].append((x, round(y, 3)))


# thirdResultOK, measure = findPairs.runFiles("rlfap/var14-f27.txt", "rlfap/dom14-f27.txt", "rlfap/ctr14-f27.txt")

# if thirdResultOK:
#     measurements['files14-f27 SAT'] = []
#     for x, y in measure.items():
#         measurements['files14-f27 SAT'].append((x, round(y, 3)))
# else:
#     measurements['files14-f27 UNSAT'] = []
#     for x, y in measure.items():
#         measurements['files14-f27 UNSAT'].append((x, round(y, 3)))

firstResultOK, secondResultOK, thirdResultOK, measure = findPairs.runFiles("rlfap/var2-f25.txt", "rlfap/dom2-f25.txt", "rlfap/ctr2-f25.txt")

if thirdResultOK:
    measurements['files2-f25 SAT'] = []
    for x, y in measure.items():
        measurements['files2-f25 SAT'].append((x, round(y, 3)))
else:
    measurements['files2-f25 UNSAT'] = []
    for x, y in measure.items():
        measurements['files2-f25 UNSAT'].append((x, round(y, 3)))

firstResultOK, secondResultOK, thirdResultOK, measure = findPairs.runFiles("rlfap/var3-f11.txt", "rlfap/dom3-f11.txt", "rlfap/ctr3-f11.txt")

if firstResultOK and secondResultOK and thirdResultOK:
    measurements['files3-f11 SAT'] = []
    for x, y in measure.items():
        measurements['files3-f11 SAT'].append((x, round(y, 3)))
else:
    measurements['files3-f11 UNSAT'] = []
    for x, y in measure.items():
        measurements['files3-f11 UNSAT'].append((x, round(y, 3)))

firstResultOK, secondResultOK, thirdResultOK, measure = findPairs.runFiles("rlfap/var8-f11.txt", "rlfap/dom8-f11.txt", "rlfap/ctr8-f11.txt")

if firstResultOK and secondResultOK and thirdResultOK:
    measurements['files8-f11 SAT'] = []
    for x, y in measure.items():
        measurements['files8-f11 SAT'].append((x, round(y, 3)))
else:
    measurements['files8-f11 UNSAT'] = []
    for x, y in measure.items():
        measurements['files8-f11 UNSAT'].append((x, round(y, 3)))

firstResultOK, secondResultOK, thirdResultOK, measure = findPairs.runFiles("rlfap/var14-f28.txt", "rlfap/dom14-f28.txt", "rlfap/ctr14-f28.txt")

if firstResultOK and secondResultOK and thirdResultOK:
    measurements['files14-f28 SAT'] = []
    for x, y in measure.items():
        measurements['files14-f28 SAT'].append((x, round(y, 3)))
else:
    measurements['files14-f28 UNSAT'] = []
    for x, y in measure.items():
        measurements['files14-f28 UNSAT'].append((x, round(y, 3)))

firstResultOK, secondResultOK, thirdResultOK, measure = findPairs.runFiles("rlfap/var6-w2.txt", "rlfap/dom6-w2.txt", "rlfap/ctr6-w2.txt")

if firstResultOK and secondResultOK and thirdResultOK:
    measurements['files6-w2 SAT'] = []
    for x, y in measure.items():
        measurements['files6-w2 SAT'].append((x, round(y, 3)))
else:
    measurements['files6-w2 UNSAT'] = []
    for x, y in measure.items():
        measurements['files6-w2 UNSAT'].append((x, round(y, 3)))



for key in measurements:
    print(key, measurements[key])


