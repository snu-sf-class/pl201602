#!/usr/bin/env python3

import os
import sys
import shutil

DELIMITER_PROBLEM = '(*=========== 3141592 ===========*)'
DELIMITER_CHECK = '(*-- Check --*)'

def PREAMBLE_PROBLEM(i):
    if i == 1:
        return 'Require Export D.\n\n'
    else:
        return 'Require Export P%02d.\n\n' % (i - 1)

def PREAMBLE_CHECK(i):
    return 'Require Import P%02d.\n\n' % i

def read_file(filename):
    with open(filename, 'r') as f:
        return f.read()

def write_file(filename, content):
    with open(filename, 'w') as f:
        return f.write(content)

if __name__ == '__main__':
    os.system('make clean')
    for file in os.listdir('.'):
        if file.endswith('.v'):
            os.remove(os.path.join(file))

    requires = read_file('requires.txt')
    write_file('Makefile', 'DFILES = D.v ' + requires + read_file('Makefile.skeleton'))
    for require in requires.split(' '):
        if require:
            shutil.copy(os.path.join('../../sf', require.rstrip()), '.')

    filename = sys.argv[1]
    content = read_file(filename)
    problems = content.split(DELIMITER_PROBLEM)

    write_file('D.v', problems[0])

    for i in range(1, len(problems)):
        problem_and_checks = problems[i].split(DELIMITER_CHECK)
        write_file('P%02d.v' % i, PREAMBLE_PROBLEM(i) + problem_and_checks[0])
        for j in range(1, len(problem_and_checks)):
            write_file('E%02d_%02d.v' % (i, j), PREAMBLE_CHECK(i) + problem_and_checks[j])
