#!/usr/bin/env python

__doc__ = """usage: twelf2tex.py <twelf_signatures.txt>
converts Twelf signatures to inference rules in the style of TAPL
"""

import re

begin_file = """
\\documentclass{article}
\\usepackage{amsmath}
\\usepackage{bcprules}
\\newcommand{\\aaatype}[0]{\\text{type}}
\\newcommand{\\aaais}[2]{\\text{#1 is #2}}
"""

begin_document = """
\\begin{document}
"""

end_document = """
\\end{document}
"""

end_file = ""

def go(twelf_txt):
  rem = twelf_txt
  commands = []
  rules = []
  while '.' in rem:
    i = rem.index('.')
    c, r = process(rem[:i])
    if c:
      commands.append(c)
    rules.append(r)
    rem = rem[i+1:]
  print begin_file
  print "\n".join(commands)
  print begin_document
  print "\n".join(rules)
  print end_document
  print end_file

def name2cmd(x):
  if x[0] == '-':
    return None
  x = x.replace("'", 'p')
  x = x.replace('-', '')
  x = x.replace('/', 'F')
  x = x.replace('0', 'Zero')
  x = x.replace('1', 'One')
  x = x.replace('2', 'Two')
  x = x.replace('3', 'Three')
  x = "aaa"+x
  return x

def typ2tex_rec(x):
  if x[0] == '(':
    i = x.index(' ')
    name = name2cmd(x[1:i])
    args = []
    rem = x[i+1:].strip()
    while rem != "" and rem[0] != ')':
      a, rem = typ2tex_rec(rem)
      args.append(a)
    if rem != "":
      rem = rem[1:].strip()
    return "{\\" + name + " " + " ".join(["{"+a+"}" for a in args]) + "}", rem
  else:
    i = 0
    n = len(x)
    while i<n and x[i] != ' ' and x[i] != ')':
      i += 1
    name = x[:i]
    if name[0].islower():
      name = "\\" + name2cmd(name)
    return name, x[i:].strip()

def typ2tex(x):
  if ' ' in x:
    x = "("+x+")"
  res, _ = typ2tex_rec(x)
  return res

def process(x):
  ic = x.index(':')
  name = x[:ic].strip()
  body = x[ic+1:].strip()
  parts = [a.strip() for a in re.split(r"}|->", body)]
  n = len(parts)-1
  premises = []
  conclusion = ""
  for i,a in enumerate(parts):
    p = ""
    if a[0] == '(':
      a = a[1:]
    if a[-1] == ')':
      a = a[:-1]
    if a[0] == '{':
      ic = a.index(':')
      varname = a[1:ic].strip()
      vartype = a[ic+1:].strip()
      p += "\\aaais {" + varname + "} {" + typ2tex(vartype) + "}"
    else:
      p += typ2tex(a)
    if i<n:
      premises.append(p)
    else:
      conclusion = p

  return new_command(name, n), new_rule(name, premises, conclusion)

def new_command(name, n):
  namecmd = name2cmd(name)
  if namecmd is None:
    return None
  args = ""
  if n>0:
    args = "(" + ",".join(["#" + str(i+1) for i in range(0, n)]) + ")"
  return "\\newcommand{\\" + namecmd + "}[" + str(n) + "]{\\text{" + name + args + "}}"

def new_rule(name, premises, conclusion):
  r = ""
  if name2cmd(name) is None:
    named = ""
  else:
    named = "[" + name + "]"
  if premises==[]:
    r += "\\infax" + named
  else:
    r += "\\infrule" + named + "{\n"
    r += "\\\\\n".join(premises)
    r += "\n}"
  r += "{"
  r += conclusion
  r += "}"
  return r

if __name__ == '__main__':
  import sys
  if len(sys.argv)!=2:
    print __doc__
  else:
    with open(sys.argv[1], 'r') as twelf_file:
      twelf_txt = twelf_file.read()
      go(twelf_txt)
